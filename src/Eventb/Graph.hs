{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Eventb.Graph where

import           Control.Arrow
import           Control.Concurrent.Async.Lifted
import           Control.DeepSeq
import           Control.Monad.Reader
import           Data.List
import qualified Data.Map.Strict                 as M
import           Data.Maybe
import           Data.Ord
import           Eventb
import Debug.Trace
import           Eventb.Predicate
import           GHC.Generics
import qualified MySet                           as S

type WP = Pred
data Vertex = V {cond :: Pred, enables :: [EventName]} deriving (Generic, NFData)
type Vertices = [Vertex]
data Edge = Edge {source :: Vertex, target :: Vertex, label :: EventName, wp :: WP} deriving (Generic, NFData)
type Edges = [Edge]
data Graph = Graph {vertices :: Vertices, edges :: Edges} deriving (Show, Generic, NFData)

instance Show Vertex where
--  show v = show $ cond v
  show v = concat ["{", intercalate "," $ enables v, "}" ,"\n",show (cond v)]
--  show v = concat ["{", intercalate "," . S.toList $ (show <$> props v), "}"]
  -- show v = concat ["{", intercalate "," $ enables v, "}"]
instance Show Edge where
  -- show e = "Edge {source = " `mappend` show (source e) `mappend`
  --               ", target = " `mappend` show (target e) `mappend`
  --               ", event = " `mappend` show (name (label e)) `mappend` "}"
  -- show e = show (label e) `mappend` "," `mappend` show (wp e)
  show = label
  -- show e = concat [label e,"\n",show (wp e)]
instance Eq Vertex where
  v1 == v2 = cond v1 == cond v2
instance Ord Vertex where
  compare = comparing cond
instance Eq Edge where
  e1 == e2 = source e1 == source e2 && target e1 == target e2 && label e1 == label e2
instance Ord Edge where
  compare e1 e2 = comparing source e1 e2 `mappend`
                  comparing target e1 e2 `mappend`
                  comparing label  e1 e2

makeEventGraph :: EventbMac -> IO Graph
makeEventGraph mac = (`runReaderT` evts) . makeGraph (invAll mac') $ fmap grd evts
  where
    mac' = completeEvent mac
    evts = events mac'

makeGraph :: Inv -> [Pred] -> ReaderT [Event] IO Graph
makeGraph  inv ps = do
  lift $ putStrLn "making vertices..."
  vs <- makeVertices inv ps
  lift $ putStrLn $ "the number of vertices is " `mappend` show (length vs)
  lift $ putStrLn "making edges..."
  es <- makeEdges vs vs
  lift $ putStrLn $ "the number of edges is " `mappend` show (length es)
  return $ Graph vs es

initVertex :: Env -> [Vertex] -> IO Vertex
initVertex env v = do
  unsatv <- mapM (isUnsatisfiable . flip runReader env . updatePred . cond) v
  return $ v !! fromJust (elemIndex False unsatv)

makeVertices :: Inv -> [Pred] -> ReaderT [Event] IO Vertices
makeVertices inv ps = mapConcurrently (makeVertex return) =<< lift (foldr (\p -> (=<<) (\acc -> filterM (fmap not . isUnsatisfiable) $ fmap (And p) acc `mappend` fmap (And (Not p)) acc)) (return [inv]) ps)

makeVertex :: (Pred -> IO Pred) -> Pred -> ReaderT [Event] IO Vertex
makeVertex minimizing p = do
  p' <- lift $ minimizing p
  enableEvts <- lift . filterM (fmap not . isUnsatisfiable . And p' . grd) =<< ask
  return V{cond = p', enables = name <$> enableEvts}

makeEdges :: Vertices -> Vertices -> ReaderT [Event] IO Edges
makeEdges vs vs' = ask >>= fmap catMaybes . lift . mapConcurrently3 (makeEdge minimizePred) vs vs'

makeEdge :: (Pred -> IO Pred) -> Vertex -> Vertex -> Event -> IO (Maybe Edge)
makeEdge minimizing src tar event
  | name event `notElem` enables src = return Nothing
  | otherwise = do
    let wpcond = cond src `And` act event `And` afterPred (cond tar)
    res <- isUnsatisfiable wpcond
    if res
      then return Nothing
      else (Just . Edge src tar (name event)) <$> minimizing wpcond

mapConcurrently3 :: (a -> b -> c -> IO d) -> [a] -> [b] -> [c] -> IO [d]
mapConcurrently3 f arg1 arg2 arg3 = mapConcurrently (uncurry3 f) $ (,,) <$> arg1 <*> arg2 <*> arg3
  where
    uncurry3 g (a, b, c) = g a b c

reachablityCheck :: S.Set Vertex -> S.Set Vertex -> Reader Graph Graph
reachablityCheck reached search
  | S.null search = do
    g <- ask
    let newedges = filter (all (`S.member` reached) . (<*>) [source, target] . pure) (edges g)
    return $ Graph (S.toList reached) newedges
  | otherwise = do
    g <- ask
    let newreached = reached `S.union` search
        newsearch = S.fromList (fmap target . filter (flip S.member search . source) $ edges g) S.\\ newreached
    reachablityCheck newreached newsearch

deleteUnreachableState :: Vertex -> Graph -> Graph
deleteUnreachableState initv = runReader (reachablityCheck S.empty (S.singleton initv))

findIncompleteInv :: Vertices -> ReaderT (Edges, [Event]) IO Vertices
findIncompleteInv [] = return []
findIncompleteInv (v:vs) = do
  lift (print v)
  (edge,evts) <- ask
  let es = filter ((==) (cond v) . cond . target) edge
  lift . print $ fmap label es
  let p = runReader (inclusionCheck v es) evts
  lift (print p)
  b <- lift $ isUnsatisfiable p
  if b
    then
      findIncompleteInv vs
    else do
      lift . putStrLn $ "There is an unreachable state."
      -- p' <- lift . minimizePred $ afterPred (cond v) `And` Not (foldr (\e -> Or (mconcat (act (label e)) `And` cond (source e))) F es)
      lift (print p)
      lift (putStrLn "------------------------------------------------")
      (:) v <$> findIncompleteInv vs

inclusionCheck :: Vertex -> Edges -> Reader [Event] Pred
inclusionCheck = foldr (\e acc -> And <$> (forany (extractVariables (cond (source e))) . Imply (cond (source e)) . Not . act . fromJust . find ((==) (label e) . name) <$> ask) <*> acc) . return . afterPred . cond




type AbstractEvent = Event
type AbstractVertex = Vertex
type AbstractVertices = Vertices
type AbstractEdge = Edge
type AbstractEdges = Edges
type ConcreteEvent = Event
type ConcreteVertex = Vertex
type ConcreteVertices = Vertices
type ConcreteEdge = Edge
type ConcreteEdges = Edges
type Relations = M.Map AbstractVertex ConcreteVertices

data RefinementGraph = RefinementGraph {abstract :: Graph, concrete :: Graph, simulation :: Relations} deriving (Show)

makeRefinementGraph :: (EventbMac, Graph) -> EventbMac -> IO RefinementGraph
makeRefinementGraph (macA, graphA) macC = (`runReaderT` events macA) . (`runReaderT` events (completeEvent macC)) . (`runReaderT` minimizePred) $ makeRefinementGraph' (invAll macC) graphA

makeRefinementGraphWithoutMinimizing :: (EventbMac, Graph) -> EventbMac -> IO RefinementGraph
makeRefinementGraphWithoutMinimizing (macA, graphA) macC = (`runReaderT` events macA) . (`runReaderT` events (completeEvent macC)) . (`runReaderT` return) $ makeRefinementGraph' (invAll macC) graphA

makeRefinementGraph' :: Inv -> Graph -> ReaderT (Pred -> IO Pred) (ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO)) RefinementGraph
makeRefinementGraph' inv graphA = do
  lift . lift . lift $ putStrLn "making vertices..."
  sim <- makeSimulation inv (vertices graphA)
  lift . lift . lift . putStrLn $ "the number of vertices is " `mappend` show (length . concat $ M.elems sim)
  lift . lift . lift $ putStrLn "making transitions..."
  e <- makeTransitions sim (edges graphA)
  lift . lift . lift . putStrLn $ "the number of transitions is " `mappend` show (length e)
  return RefinementGraph{abstract = graphA, concrete = Graph (foldr mappend [] sim) e, simulation = sim}

makeSimulation :: Inv -> AbstractVertices -> ReaderT (Pred -> IO Pred) (ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO)) Relations
makeSimulation inv vs = do
  base <- lift $ newEvents >>= lift . lift . makeBaseVertices inv . fmap grd
  grp <- mapConcurrently (makeRefinementVertices base) vs
  return . M.fromList $ zip vs grp

newEvents :: ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO) [Event]
newEvents = ask >>= lift . filterM (fmap not . isRefined)

isRefined :: Event -> ReaderT [AbstractEvent] IO Bool
isRefined evt = do
  abstevts <- ask
  if evt `elem` abstevts
    then return True
    else foldM ((. isRefined) . fmap . (||)) False (refine evt)

makeBaseVertices :: Inv -> [Grd] -> IO [Pred]
makeBaseVertices = foldr (\g -> (=<<) (filterM (fmap not . isUnsatisfiable) . uncurry mappend . (fmap (And g) &&& fmap (And (Not g))))) . return . replicate 1

makeRefinementVertices :: [Pred] -> AbstractVertex -> ReaderT (Pred -> IO Pred) (ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO)) ConcreteVertices
makeRefinementVertices base v = do
  enabledRefineEvts <- lift $ ask >>= lift . filterM (\e -> ask >>= lift . runReaderT (isRefined e) . filter ((`elem` enables v) . name))
  let ps = foldr (\evt -> uncurry mappend . (fmap (And (grd evt)) &&& fmap (And (Not (grd evt))))) [cond v] enabledRefineEvts
  refinementVertices <- lift . lift . lift $ concat <$> mapConcurrently (filterM (fmap not . isUnsatisfiable) . (`fmap` ps) . And) base
  ask >>= \minimizing -> lift $ mapConcurrently (\vertex -> ask >>= lift . lift . runReaderT (makeVertex minimizing vertex)) refinementVertices

makeTransitions :: Relations -> AbstractEdges -> ReaderT (Pred -> IO Pred) (ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO)) ConcreteEdges
makeTransitions sim abstractEdges = mappend <$> (concat <$> mapConcurrently (makeRefineTransitions sim) abstractEdges) <*> (concat <$> mapConcurrently makeNewTransitions (M.elems sim))

makeRefineTransitions :: Relations -> AbstractEdge -> ReaderT (Pred -> IO Pred) (ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO)) ConcreteEdges
makeRefineTransitions sim e = do
  refineEvts <- lift $ ask >>= lift . filterM (\e' -> ask >>= lift . runReaderT (isRefined e') . replicate 1 . fromJust . find ((==) (label e) . name))
  ask >>= \minimizing -> lift . lift . lift $ catMaybes <$> mapConcurrently3 (makeEdge minimizing) (sim M.! source e) (sim M.! target e) refineEvts

makeNewTransitions :: ConcreteVertices -> ReaderT (Pred -> IO Pred) (ReaderT [ConcreteEvent] (ReaderT [AbstractEvent] IO)) ConcreteEdges
makeNewTransitions subvertices = ask >>= \minimizing -> lift $ newEvents >>= lift . lift . fmap catMaybes . mapConcurrently3 (makeEdge minimizing) subvertices subvertices

makeEventGraphKai :: (EventbMac, Graph) -> EventbMac -> IO Graph
makeEventGraphKai (macA, graphA) macC = do
  refinementGraph <- makeRefinementGraphWithoutMinimizing (macA, graphA) macC
  runReaderT (mergeRefinementGraph (concrete refinementGraph)) (events $ completeEvent macC)

mergeRefinementGraph :: Graph -> ReaderT [ConcreteEvent] IO Graph
mergeRefinementGraph g = do
  lift $ putStrLn "making vertices..."
  verticesMap <- lift . mapConcurrently minimizePred . mergeVertices $ vertices g
  let newMap = M.mapWithKey (flip V) verticesMap
  lift . putStrLn $ "the number of vertices is " `mappend` show (M.size newMap)
  lift $ putStrLn "making transitions..."
  newEdges <- mapConcurrently modifyWp . S.toList . foldr (S.insert . (\e -> e{source = newMap M.! enables (source e), target = newMap M.! enables (target e), wp = T})) S.empty $ edges g
  lift . putStrLn $ "the number of transitions is " `mappend` show (length newEdges)
  return $ Graph (M.elems newMap) newEdges
  where
    modifyWp e = do
      evt <- fromJust . find (\evt -> label e == name evt) <$> ask
      newWp <- lift . minimizePred $ cond (source e) `And` act evt `And` cond (target e)
      return e{wp = newWp}

mergeVertices :: ConcreteVertices -> M.Map [EventName] Pred
mergeVertices [] = M.empty
mergeVertices (v:vs) = add v $ mergeVertices vs
  where
    add u m = if M.notMember (enables u) m
      then M.insert (enables u) (cond u) m
      else M.adjust (`Or` cond u) (enables u) m




{-
-- this implement is very very dirty
unifyedges :: [Edge] -> [(Vertex, Vertex, [(String, Pred)])]
unifyedges = fmap unify . groupBy (\e1 e2 -> source e1 == source e2 && target e1 == target e2, )
  where
    plus e1 e2 = (source e1, target e2, )
    unify list = (source $ head list, target $ head list, intercalate "," $ fmap label list)

-}
{-
-- conver to conjunctive normal form in order to clarify, minimize
data AP = Eq E.AExp E.AExp | Gt E.AExp E.AExp | Not AP deriving Show
type Or = [AP]
type And = [Or]
type Pred = And


showAP :: AP -> String
showAP (Eq a1 a2) = concat [show a1,"=",show a2]
showAP (Gt a1 a2) = concat [show a1,">",show a2]
showAP (Not b)    = "not" `mappend` showAP b
showOr :: Or -> String
showOr [] = "F"
showOr p  = concat ["(",intercalate " | " . fmap showAP $ p,")"]
showAnd :: And -> String
showAnd [] = "T"
showAnd p  = intercalate " & " . fmap showOr $ p
showPred :: Pred -> String
showPred = showAnd

pnot :: Pred -> Pred
pnot = merge . fmap (fmap Not)
por :: Pred -> Pred -> Pred
por p1 p2 = concat <$> merge [p1,p2]
pand :: Pred -> Pred -> Pred
pand = mappend
merge []     = [[]]
merge (x:xs) = x >>= \y -> fmap (y:) (merge xs)


predToPredicate :: E.Pred -> Pred
predToPredicate E.T             = []
predToPredicate E.F             = [[]]
predToPredicate (E.Eq a1 a2)    = [[Eq a1 a2]]
predToPredicate (E.Gt a1 a2)    = [[Gt a1 a2]]
predToPredicate (E.And b1 b2)   = predToPredicate b1 `mappend` predToPredicate b2
predToPredicate (E.Or b1 b2)    = por (predToPredicate b1) (predToPredicate b2)
predToPredicate (E.Not b)       = pnot $ predToPredicate b
predToPredicate (E.Imply b1 b2) = predToPredicate (E.Not b1 `E.Or` b2)

minimizePred :: Pred -> IO Pred
minimizePred p = do
  let p' = fmap (fmap minimizeAP) p
  p'' <- evalStateT (orEliminate p') []
  evalStateT (andEliminate p'') []

minimizeAP :: AP -> AP
minimizeAP (Not (Not p)) = p
minimizeAP p             = p

orEliminateSub :: Or -> ReaderT And (StateT Or IO) Or
orEliminateSub [] = get
orEliminateSub (p:ps) = do
  c <- ask
  ps' <- get
  let notb = fmap (replicate 1 . Not) $ ps `mappend` ps'
  tf <- liftIO . isUnsatisfiable $ concat [[[p]], notb, c]
  if tf
    then orEliminateSub ps
    else do
      put $ p:ps'
      orEliminateSub ps

orEliminate :: Pred -> StateT And IO Pred
orEliminate [] = get
orEliminate (p:ps) = do
  qs <- get
  q <- liftIO $ execStateT (runReaderT (orEliminateSub p) (qs `mappend` ps)) []
  put $ q:qs
  orEliminate ps

andEliminate :: Pred -> StateT And IO Pred
andEliminate [] = get
andEliminate (p:ps) = do
  ps' <- get
  let nota = fmap (replicate 1 . Not) p
      b = ps `mappend` ps'
  tf <- liftIO . isUnsatisfiable $ nota `mappend` b
  if tf
    then andEliminate ps
    else do
      put $ p:ps'
      andEliminate ps

isUnsatisfiable :: Pred -> IO Bool
isUnsatisfiable p = do
  res <- sat $ do
    let vars = varsInPred p
    sints <- sIntegers vars
    runReaderT (predToPredicateicate p) (M.fromList $ zip vars sints)
  return . not . modelExists $ res

extractAExpVar :: E.AExp -> S.Set String
extractAExpVar (E.AInt i) = S.empty
extractAExpVar (E.AVar v) = S.singleton v
extractAExpVar (E.Add a1 a2) = extractAExpVar a1 `S.union` extractAExpVar a2
extractAExpVar (E.Sub a1 a2) = extractAExpVar a1 `S.union` extractAExpVar a2
extractAExpVar (E.Mul a1 a2) = extractAExpVar a1 `S.union` extractAExpVar a2
extractAExpVar (E.Div a1 a2) = extractAExpVar a1 `S.union` extractAExpVar a2

varsInAP :: AP -> S.Set String
varsInAP (Eq a1 a2) = extractAExpVar a1 `S.union` extractAExpVar a2
varsInAP (Gt a1 a2) = extractAExpVar a1 `S.union` extractAExpVar a2
varsInAP (Not b)    = varsInAP b

varsInPred :: Pred -> [String]
varsInPred = S.toList . foldr (S.union . foldr (S.union . varsInAP) S.empty) S.empty

aExpToSInt :: E.AExp -> ReaderT (M.Map String SInteger) Symbolic SInteger
aExpToSInt (E.AInt i)    = return $ fromIntegral i
aExpToSInt (E.AVar v)    = do
  env <- ask
  return . fromJust $ M.lookup v env
aExpToSInt (E.Add a1 a2) = do
  i1 <- aExpToSInt a1
  i2 <- aExpToSInt a2
  return $ i1 + i2
aExpToSInt (E.Sub a1 a2) = do
  i1 <- aExpToSInt a1
  i2 <- aExpToSInt a2
  return $ i1 - i2
aExpToSInt (E.Mul a1 a2) = do
  i1 <- aExpToSInt a1
  i2 <- aExpToSInt a2
  return $ i1 * i2
aExpToSInt (E.Div a1 a2) = do
  i1 <- aExpToSInt a1
  i2 <- aExpToSInt a2
  return $ i1 `sDiv` i2

apToPredicate :: AP -> ReaderT (M.Map String SInteger) Symbolic SBool
apToPredicate (Eq a1 a2) = do
  i1 <- aExpToSInt a1
  i2 <- aExpToSInt a2
  return $ i1 .== i2
apToPredicate (Gt a1 a2) = do
  i1 <- aExpToSInt a1
  i2 <- aExpToSInt a2
  return $ i1 .< i2
apToPredicate (Not b) = do
  b' <- apToPredicate b
  return $ bnot b'

orToPredicate :: Or -> ReaderT (M.Map String SInteger) Symbolic SBool
orToPredicate p = do
  ps <- mapM apToPredicate p
  return $ bOr ps

andToPredicate :: And -> ReaderT (M.Map String SInteger) Symbolic SBool
andToPredicate p = do
  ps <- mapM orToPredicate p
  return $ bAnd ps

predToPredicateicate :: Pred -> ReaderT (M.Map String SInteger) Symbolic SBool
predToPredicateicate = andToPredicate


--to make Graph
type Vertex = Pred
type Edge = (Vertex, Vertex, E.Event, Pred)
type Graph = ([Vertex],[Edge])
source :: Edge -> Vertex
source (s,_,_,_) = s
target :: Edge -> Vertex
target (_,t,_,_) = t
label :: Edge -> E.Event
label (_,_,event,_) = event
weakestPrecondition :: Edge -> Pred
weakestPrecondition (_,_,_,b) = b

vertices :: E.EventbMac -> [Vertex]
vertices mac = fmap predToPredicate . foldr (\x y -> fmap (E.And x) y `mappend` fmap (E.And (E.Not x)) y) [invaxiom] $ allgrd
  where
    allgrd = mconcat . E.grd <$> E.events mac
    invaxiom = mconcat (E.inv mac) `E.And` (mconcat . fmap (mconcat . E.axiom))  (E.sees mac)

combination2 :: [a] -> [(a, a)]
combination2 list = foldr (\x y -> fmap ((,) x) list `mappend` y) [] list

updateAExp :: E.AExp -> Reader E.Env E.AExp
updateAExp (E.AInt i) = return $ E.AInt i
updateAExp (E.AVar v) = do
  env <- ask
  case M.lookup v env of
    Just (VAExp value) -> return value
    Nothing    -> return $ E.AVar v
updateAExp (E.Add a1 a2) = do
  i1 <- updateAExp a1
  i2 <- updateAExp a2
  return $ E.Add i1 i2
updateAExp (E.Sub a1 a2) = do
  i1 <- updateAExp a1
  i2 <- updateAExp a2
  return $ E.Sub i1 i2
updateAExp (E.Mul a1 a2) = do
  i1 <- updateAExp a1
  i2 <- updateAExp a2
  return $ E.Mul i1 i2
updateAExp (E.Div a1 a2) = do
  i1 <- updateAExp a1
  i2 <- updateAExp a2
  return $ E.Div i1 i2

updateAP :: AP -> Reader E.Env AP
updateAP (Eq a1 a2) = do
  a1' <- updateAExp a1
  a2' <- updateAExp a2
  return $ Eq a1' a2'
updateAP (Gt a1 a2) = do
  a1' <- updateAExp a1
  a2' <- updateAExp a2
  return $ Gt a1' a2'
updateAP (Not p) = do
  p' <- updateAP p
  return $ Not p'

updateOr :: Or -> Reader E.Env Or
updateOr = mapM updateAP

updateAnd :: And -> Reader E.Env And
updateAnd = mapM updateOr

updatePred :: Pred -> Reader E.Env Pred
updatePred = updateAnd

execEvent :: E.Event -> Pred -> Pred
execEvent = flip (runReader . updatePred) . E.act

isTransible :: (Vertex, Vertex) -> E.Event -> IO (Maybe Edge)
isTransible (src,tar) event = do
  let wp = execEvent event tar
  tf <- isUnsatisfiable $ src `pand` wp
  if tf
    then return Nothing
    else return $ Just (src,tar,event,wp)

makeGraph :: E.EventbMac -> IO Graph
makeGraph mac = do
  v <- mapM minimizePred $ vertices mac
  edges <- catMaybes <$> mapM (uncurry isTransible) ((,) <$> combination2 v <*> E.events mac)
  return (v, edges)


-}
