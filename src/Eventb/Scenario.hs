{-# LANGUAGE DuplicateRecordFields #-}

module Eventb.Scenario  where

import qualified Control.Arrow        as A
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.List
import qualified Data.Map.Strict      as M
import           Data.Maybe
import           Data.SBV             hiding (isSatisfiable, label, name)
import qualified MySet                as S
--import           Debug.Trace
import           Eventb
import           Eventb.Dot
import           Eventb.Graph
import           Eventb.Predicate
import           System.IO
import           System.Process


data Path = Path {path :: [Edge], past :: Edges}
data Info = Info {edges :: Edges, initcond :: Pred, initvertex :: Vertex}
newtype Scenario = Scenario {scenario :: (Path, [(String,Value)])}
newtype Scenarios = Scenarios {scenarios :: [Scenario]}
instance Show Path where
  show = intercalate " -> " . fmap label . path
instance Show Scenario where
  show s = concat [ "initial environment:\n"
                  , showEnv env
                  , "------------------------------------------------\n"
                  , show path
                  , "\n"]
    where
      (path, env) = scenario s
      showEnv = (=<<) (\(var,val) -> concat [var, " = ", show val, "\n"])
instance Show Scenarios where
  show s = evalState (show' $ scenarios s) 0
    where
      show' [] = return ""
      show' (t:ts) = do
        i <- get
        put $ i+1
        rest <- show' ts
        return $ concat ["Scenario",show i,":\n",show t,"\n",rest]

initPred :: EventbMac -> Pred
initPred = M.foldrWithKey f T . initenv
  where
    f key v@(AExp _) p  = (AP $ AExp (AVar (Var key)) `Eq` v) `And` p
    f key v@(BExp _) p  = (AP $ BExp (BVar (Var key)) `Eq` v) `And` p
    f key v@(Color _) p = (AP $ Color (CVar (Var key)) `Eq` v) `And` p

passedEdge :: Scenario -> Edges
passedEdge s = path . fst $ scenario s

updatePath :: Path -> Edge -> Path
updatePath p e = Path{path = e : path p, past = e : past p}

renameVar :: Var -> State Int Var
renameVar (Var v) = do
  i <- get
  return . Var $ v `mappend` show i
renameVar (NewVar v) = do
  i <- get
  return . Var $ v `mappend` show (i + 1)
renameVar (Const c) = return $ Const c

renameVarForAExp :: AExp -> State Int AExp
renameVarForAExp (AVar v) = do
  v' <- renameVar v
  return $ AVar v'
renameVarForAExp (Add a1 a2) = do
  a1' <- renameVarForAExp a1
  a2' <- renameVarForAExp a2
  return $ Add a1' a2'
renameVarForAExp (Sub a1 a2) = do
  a1' <- renameVarForAExp a1
  a2' <- renameVarForAExp a2
  return $ Sub a1' a2'
renameVarForAExp (Mul a1 a2) = do
  a1' <- renameVarForAExp a1
  a2' <- renameVarForAExp a2
  return $ Mul a1' a2'
renameVarForAExp (Div a1 a2) = do
  a1' <- renameVarForAExp a1
  a2' <- renameVarForAExp a2
  return $ Div a1' a2'
renameVarForAExp a = return a

renameVarForBExp :: BExp -> State Int BExp
renameVarForBExp (BVar v) = do
  v' <- renameVar v
  return $ BVar v'
renameVarForBExp b = return b

renameVarForColor :: Eventb.Color -> State Int Eventb.Color
renameVarForColor (CVar v) = do
  v' <- renameVar v
  return $ CVar v'
renameVarForColor c = return c

renameVarForValue :: Value -> State Int Value
renameVarForValue (AExp a)  = AExp <$> renameVarForAExp a
renameVarForValue (BExp b)  = BExp <$> renameVarForBExp b
renameVarForValue (Color c) = Color <$> renameVarForColor c

renameVarForAP :: AP -> State Int AP
renameVarForAP (Eq v1 v2) = do
  v1' <- renameVarForValue v1
  v2' <- renameVarForValue v2
  return $ Eq v1' v2'
renameVarForAP (Gt a1 a2) = do
  a1' <- renameVarForAExp a1
  a2' <- renameVarForAExp a2
  return $ Gt a1' a2'


renameVarForPred :: Pred -> State Int Pred
renameVarForPred T = return T
renameVarForPred F = return F
renameVarForPred (AP p) = AP <$> renameVarForAP p
renameVarForPred (And b1 b2) = do
  b1' <- renameVarForPred b1
  b2' <- renameVarForPred b2
  return $ And b1' b2'
renameVarForPred (Or b1 b2) = do
  b1' <- renameVarForPred b1
  b2' <- renameVarForPred b2
  return $ Or b1' b2'
renameVarForPred (Not b) = do
  b' <- renameVarForPred b
  return $ Not b'
renameVarForPred (Imply b1 b2) = do
  b1' <- renameVarForPred b1
  b2' <- renameVarForPred b2
  return $ Imply b1' b2'

currentPred :: Path -> Pred
currentPred = flip evalState 0 . foldr f (return T) . path
  where
    f e s = do
      p <- renameVarForPred $ wp e
      modify (1 +)
      p' <- s
      return $ And p p'

isSatisfiable :: Pred -> IO (Maybe [(String,Value)])
isSatisfiable b = do
  let vars = extractVariables b
      aExpVars = S.toList $ aExp (vars :: Vars)
      bExpVars = S.toList $ bExp (vars :: Vars)
      colorVars = S.toList $ color (vars :: Vars)
  res <- sat $ do
    smap <- varsToSMap vars
    runReaderT (predToPredicate b) smap
  case extractModel res :: Maybe ([Integer], [Bool], [Eventb.Predicate.Color]) of
    Just (aExps, bExps, colors) -> return . Just $
                zip aExpVars (fmap (AExp . AInt) aExps) `mappend`
                zip bExpVars (fmap (BExp . boolToBExp) bExps) `mappend`
                zip colorVars (fmap (Color . colorToColor) colors)
    Nothing   -> return Nothing


-- check satisfiable
saisfiabiltyCheck :: Path -> IO Bool
saisfiabiltyCheck p = do
  let cp = currentPred p
  not <$> isUnsatisfiable cp

backOneEvent :: Path -> ReaderT Info IO [Path]
backOneEvent p = do
  info <- ask
  let enables = filter (\e -> source (head (path p)) == target e {- && e `notElem` past -}) $ edges (info :: Info)
      paths = fmap (updatePath p) enables
  lift . filterM saisfiabiltyCheck $ paths

-- improve the number of asking SMT; not too many SMT. now no ask
searchScenarioThrough :: [Path] -> StateT Int (ReaderT Info IO) (Maybe Scenario)
searchScenarioThrough paths = do
  info <- ask
  let srcIsInit = filter ((==) (initvertex info) . source . head . path) paths
  res <- lift . lift . fmap (catMaybes . zipWith (fmap . (,)) srcIsInit). mapM (isSatisfiable . And (initcond info) . currentPred) $ srcIsInit
  case res of
    x:xs -> return . Just $ Scenario x
    []   -> do
      next <- concat <$> mapM (lift . backOneEvent) paths
      lift . lift . print $ length next
--      lift . print $ next
      i <- get
      if null next || i > 15
        then return Nothing
        else put (i+1) >> searchScenarioThrough next

searchScenarios :: Edges -> StateT Edges (ReaderT Info IO) [Scenario]
searchScenarios [] = return []
searchScenarios (e:es) = do
    lift . lift . putStrLn $ "now searching:\n" `mappend` show e
    m <- lift $ evalStateT (searchScenarioThrough [Path {path = [e], past = [e]}]) 0
    lift . lift $ putStrLn "Done"
    case m of
      Nothing -> do
        modify (insert e)
        searchScenarios es
      Just s -> do
        let x = passedEdge s
            rest = es \\ x
        s' <- searchScenarios rest
        let y = foldr (S.union . S.fromList . passedEdge) S.empty s'
        if S.fromList x `S.isSubsetOf` y
          then return s'
          else return $ s:s'

makeScenario :: EventbMac -> IO Scenarios
makeScenario mac = do
  putStrLn "making Graph..."
  g <- makeEventGraph mac
  initv <- initVertex (initenv mac) $ vertices g
  putStrLn "Done"
  putStrLn "delete unreachable states..."
  let g' = deleteUnreachableState initv g
      remove = edges (g :: Graph) \\ edges (g' :: Graph)
  putStrLn "Done"
  putStrLn "making scenarios..."
  let info = Info {edges = filter (uncurry (/=) . (source A.&&& target)) $ edges (g' :: Graph), initcond = initPred mac, initvertex = initv}
  (s, remove') <- runReaderT (runStateT (searchScenarios (edges (g' :: Graph))) []) info
  putStrLn $ "remove edges:\n" `mappend` show remove'
  putStrLn "write graph..."
  writeGraph (macname mac `mappend` "3") (Graph (vertices g') (edges (g :: Graph) \\ (remove `mappend` remove'))) initv
  putStrLn "Done"
  return $ Scenarios s
{-
searchScenarioThrough' :: [Path] -> ReaderT Info IO (Maybe Scenario)
searchScenarioThrough' paths = do
  info <- ask
  let srcIsInit = filter ((==) (initvertex info) . source . head . path) paths
  res <- lift . fmap (catMaybes . zipWith (fmap . (,)) srcIsInit). mapM (isSatisfiable . And (initcond info) . currentPred) $ srcIsInit
  case res of
    x:xs -> return . Just $ Scenario x
    []   -> do
      next <- concat <$> mapM backOneEvent paths
      lift . print $ length next
      lift (print next)
      searchScenarioThrough' next

edgeExistCheck :: Pred -> Edge -> ReaderT Info IO Bool
edgeExistCheck p e = do
  lift $ print e
  let e' = e{wp = wp e `And` p}
  res <- searchScenarioThrough' [Path {path = [e'], past = [e']}]
  case res of
    Just _  -> return True
    Nothing -> return False

edgesExistCheck :: [Pred] -> Edges -> ReaderT Info IO [Edges]
edgesExistCheck ps es = mapM (\p -> do {lift (print p); flip filterM es (edgeExistCheck p)}) ps

test :: EventbMac -> [Pred] -> IO ()
test mac ps = do
  let mac' = completeEvent mac
  g <- makeEventGraph mac'
  putStrLn "Search existing edges..."
  initv <- initVertex (initenv mac') (vertices g)
  let info = Info {edges = edges (g :: Graph), initcond = initPred mac', initvertex = initv}
  res <- runReaderT (edgesExistCheck ps (edges (g :: Graph))) info
  print $ zip ps res
-}
{-
existChangedVarAExp :: Monad m => AExp -> ReaderT Env m Bool
existChangedVarAExp (AInt _) = return False
existChangedVarAExp (AVar v) = fmap (M.member v) ask
existChangedVarAExp (Add a1 a2) = (||) <$> existChangedVarAExp a1 <*> existChangedVarAExp a2
existChangedVarAExp (Sub a1 a2) = (||) <$> existChangedVarAExp a1 <*> existChangedVarAExp a2
existChangedVarAExp (Mul a1 a2) = (||) <$> existChangedVarAExp a1 <*> existChangedVarAExp a2
existChangedVarAExp (Div a1 a2) = (||) <$> existChangedVarAExp a1 <*> existChangedVarAExp a2

existChangedVarBExp :: Monad m => BExp -> ReaderT Env m Bool
existChangedVarBExp (BVar v) = fmap (M.member v) ask
existChangedVarBExp _        = return False

existChangedVarColor :: Monad m => Eventb.Color -> ReaderT Env m Bool
existChangedVarColor (CVar v) = fmap (M.member v) ask
existChangedVarColor _        = return False

abstractPred :: Pred -> ReaderT Env (ReaderT SMap Symbolic) SBool
abstractPred T = return true
abstractPred F = return false
abstractPred (Eq (AExp a1) (AExp a2)) = do
  b <- (||) <$> existChangedVarAExp a1 <*> existChangedVarAExp a2
  if b
    then lift . lift $ sBool "EQ"
    else do
      a1' <- lift $ aExpToSInt a1
      a2' <- lift $ aExpToSInt a2
      return $ a1' .== a2'
abstractPred (Eq (BExp b1) (BExp b2)) = do
  b <- (||) <$> existChangedVarBExp b1 <*> existChangedVarBExp b2
  if b
    then lift . lift $ sBool "EQ"
    else do
      b1' <- lift $ bExpToSBool b1
      b2' <- lift $ bExpToSBool b2
      return $ b1' .== b2'
abstractPred (Eq (Color c1) (Color c2)) = do
  b <- (||) <$> existChangedVarColor c1 <*> existChangedVarColor c2
  if b
    then lift . lift $ sBool "EQ"
    else do
      c1' <- lift $ colorToSColor c1
      c2' <- lift $ colorToSColor c2
      return $ c1' .== c2'
abstractPred (Gt a1 a2) = do
  b <- (||) <$> existChangedVarAExp a1 <*> existChangedVarAExp a2
  if b
    then lift . lift $ sBool "GT"
    else do
      a1' <- lift $ aExpToSInt a1
      a2' <- lift $ aExpToSInt a2
      return $ a1' .> a2'
abstractPred (And b1 b2) = do
  b <- abstractPred b1
  b' <- abstractPred b2
  return $ b &&& b'
abstractPred (Or b1 b2) = do
  b <- abstractPred b1
  b' <- abstractPred b2
  return $ b ||| b'
abstractPred (Not b) = do
  b' <- abstractPred b
  return $ bnot b'
abstractPred (Imply b1 b2) = do
  b <- abstractPred b1
  b' <- abstractPred b2
  return $ b ==> b'

changedEnvAfterLoop :: [Edge] -> Env
changedEnvAfterLoop =  foldr (\new -> (`M.union` new) . M.map (flip runReader new . updateValue)) M.empty . fmap (act . label)




-}
