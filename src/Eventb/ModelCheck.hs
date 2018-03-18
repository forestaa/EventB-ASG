{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonadComprehensions        #-}

module Eventb.ModelCheck where

import           Control.Arrow
import           Control.Concurrent.Async.Lifted
import           Control.Monad.Reader
import           Data.Graph                      (SCC (..), stronglyConnComp)
import           Data.List
import qualified Data.Map.Strict                 as M
import           Data.Maybe
import           Debug.Trace
import           Eventb
import qualified Eventb.Graph                    as G
import           Eventb.LTL.Buchi                hiding (isempty)
import           Eventb.LTL.LTL
import           Eventb.LTL.Type
import qualified MySet                           as S
import           System.Process

-- Assumption: All states are reachable.
modelCheck :: EventbMac -> LTL AP -> IO ()
modelCheck mac ltl = do
  let mac' = completeEvent mac
  -- g' <- G.makeEventGraph mac'
  -- initv <- G.initVertex (initenv mac') (G.vertices g')
  -- G.writeGraph (macname mac') g' initv
  (g,initv) <- makeLTLGraph mac' ltl
--  G.writeGraph (macname mac' `mappend` "_" `mappend` filter (/= ',') (show apset)) g initv
  putStrLn "write a graph with atomic propositions"
  putStrLn "model checking..."
  let b = optimizeBuchi $ intersectionBetweenGraphAndLTL (events mac') g initv (Eventb.LTL.LTL.Not ltl)
  case runReader (sccWithFinalAndOrdinary . stronglyConnComp $ buchiToGraph b) b of
    [] ->
      putStrLn "result: true"
  --     let b_name = macname mac' `mappend` "_" `mappend` show (Eventb.LTL.LTL.Not ltl)
  --     writeBuchiInDot b_name b
  --     putStrLn $ "write a complete buchi automaton: " `mappend` b_name
  --     let b_ltl = ltlToBuchi (Eventb.LTL.LTL.Not ltl)
  --     writeBuchiInDot (show $ Eventb.LTL.LTL.Not ltl) b_ltl
  --     putStrLn $ "write a ltl automaton: " `mappend` show (Eventb.LTL.LTL.Not ltl)
    sccs -> do
      putStrLn "result: possible false"
      putStrLn "following automata possibly have ErrorPaths"
      let b_name = macname mac' `mappend` "_" `mappend` rename (show (Eventb.LTL.LTL.Not ltl))
  --    writeBuchiInDot b_name b
      putStrLn $ "write a complete buchi automaton: " `mappend` b_name
      let b_ltl = ltlToBuchi (Eventb.LTL.LTL.Not ltl)
  --    writeBuchiInDot (rename . show $ Eventb.LTL.LTL.Not ltl) b_ltl
      putStrLn $ "write a ltl automaton: " `mappend` show (Eventb.LTL.LTL.Not ltl)
      mapM_ (\(scc,i) -> do
        let b_name = concat [macname mac', "_", rename $ show (Eventb.LTL.LTL.Not ltl), "_", show i]
    --    writeBuchiInDot b_name $ sccToBuchi b scc
        putStrLn $ "write a scc: " `mappend` b_name)
        $ zip sccs [0..]

rename :: String -> String
rename = (=<<) gt
  where
    gt '>' = "_Gt_"
    gt c   = [c]

newtype LTLState = LTLState {ltlv :: (G.Vertex, (States (LTL AP), States (LTL AP)))} deriving (Eq, Ord)

instance Show LTLState where
  show  = show . fst . ltlv
-- show = show . ltlv

makeLTLGraph :: EventbMac -> LTL AP -> IO (G.Graph,G.Vertex)
makeLTLGraph mac ltl = do
  putStrLn "make graph for LTL..."
  v <- runReaderT (makeVerticesForLTL (vars mac) ltl (G.collectInv mac) (mconcat . grd <$> events mac)) (events mac)
  putStrLn $ "the number of vetices is " `mappend` show (length v)
  e <- fmap concat . mapConcurrently (uncurry G.makeEdges) $ (,) <$> v <*> v
  let g = G.Graph v e
  initv <- G.initVertex (initenv mac) (G.vertices g)
  return (g,initv)

makeVerticesForLTL :: Vars -> LTL AP -> Inv -> [Pred] -> ReaderT [Event] IO [G.Vertex]
makeVerticesForLTL v ltl inv ps = do
  vs <- G.makeVertices inv ps
  let finiteSetPred = S.toList . S.map ((mconcat &&& S.fromList) . fmap AP) . S.directproduct $ S.foldr ((:) . bExpAllPred) [] (bExp v) `mappend` S.foldr ((:) . colorAllPred) [] (color v)
  vs' <- lift $ addAPCondsToVertices' vs finiteSetPred
  let apset = foldr (\p acc -> fmap (And p *** S.insert p) acc `mappend` fmap (first $ And (Eventb.Not p)) acc) [(T,S.empty)] . S.toList . S.map AP $ extendAExpProp =<< membersInLTL ltl
  lift $ print apset
  lift $ addAPCondsToVertices' vs' apset

addAPCondsToVertices :: G.Vertices -> [(Pred,S.Set Pred)] -> IO G.Vertices
addAPCondsToVertices v ps = fmap (filter ((/=) F . G.cond)) . mapConcurrently (uncurry addAPCond) $ (,) <$> v <*> ps

addAPCondsToVertices' :: G.Vertices -> [(Pred,S.Set Pred)] -> IO G.Vertices
addAPCondsToVertices' v ps = fmap catMaybes . mapConcurrently (uncurry addAPCond') $ (,) <$> v <*> ps


bExpAllPred :: String -> S.Set AP
bExpAllPred s = S.fromList [BExp (var s) `Eq` BExp TRUE, BExp (var s) `Eq` BExp FALSE]

colorAllPred :: String -> S.Set AP
colorAllPred s = S.fromList [Color (var s) `Eq` Color Red, Color (var s) `Eq` Color Green]

extendAExpProp :: AP -> S.Set AP
extendAExpProp (Eq (AExp a) (AExp a')) = S.fromList [Eq (AExp a) (AExp a'), Gt a a']
--extendAExpProp (Gt a a') = S.fromList [Eq (AExp a) (AExp a'), Gt a a']
extendAExpProp p = S.singleton p

addAPCond :: G.Vertex -> (Pred,S.Set Pred) -> IO G.Vertex
addAPCond v (p,ps) = do
  let newcond = G.cond v `And` p
  res <- G.minimizePred newcond
  return v{G.cond = res, G.props = G.props v `S.union` ps}

addAPCond' :: G.Vertex -> (Pred,S.Set Pred) -> IO (Maybe G.Vertex)
addAPCond' v (p,ps) = do
  let newcond = G.cond v `And` p
  b <- G.isUnsatisfiable newcond
  if b
    then return Nothing
    else return $ Just v{G.cond = newcond, G.props = G.props v `S.union` ps}


intersectionBetweenGraphAndLTL :: [Event] -> G.Graph -> G.Vertex -> LTL AP -> Buchi Event LTLState
intersectionBetweenGraphAndLTL evts g initv ltl = Buchi (S.fromList evts) s s0 edge f
  where
    v = S.fromList $ G.vertices g
    e = S.fromList $ G.edges g
    b = ltlToBuchi ltl
    s = fmap LTLState ((,) <$> v <*> states b)
    s0 = fmap LTLState ((,) <$> S.singleton initv <*> initial b)
    edge = s >>= computeTransition (S.concat $ alpha b) (transition b) e
    f = fmap LTLState ((,) <$> v <*> final b)

computeTransition :: S.Set AP -> Edges (S.Set AP) (States (LTL AP), States (LTL AP)) -> S.Set G.Edge ->  LTLState -> Edges Event LTLState
computeTransition a ltledges graphedges (LTLState (s,ls)) =
  [ Edge (LTLState (s,ls)) (LTLState (s',ls')) evt | (ls',ps) <- possibleLTLTargets, (s',evt) <- possibleGraphTargets, (AP <$> ps) == S.intersection (AP <$> a) (G.props s') ]
  where
    possibleLTLTargets = (target &&& label) <$> S.filter ((==) ls . source) ltledges
    possibleGraphTargets = (G.target &&& G.label) <$> S.filter ((==) s . G.source) graphedges

buchiToGraph :: (Ord a, Ord s) => Buchi a s -> [(s, s, [s])]
buchiToGraph b = (\s -> (s,s, S.toList . S.map target $ S.filter ((==) s . source) (transition b))) <$> S.toList (states b)

sccWithFinalAndOrdinary :: [SCC LTLState] -> Reader (Buchi Event LTLState) [Buchi Event LTLState]
sccWithFinalAndOrdinary [] = return []
sccWithFinalAndOrdinary (AcyclicSCC _ : sccs) = sccWithFinalAndOrdinary sccs
sccWithFinalAndOrdinary (CyclicSCC s : sccs) = do
  b <- ask
  let b' = sccToBuchi b $ S.fromList s
  if foldr ((||) . flip S.member (final b)) False s && isThereOrdinary b'
    then (:) b' <$> sccWithFinalAndOrdinary sccs
    else sccWithFinalAndOrdinary sccs

sccToBuchi :: (Ord a, Ord s) => Buchi a s -> States s -> Buchi a s
sccToBuchi b s = Buchi (alpha b) s S.empty e f
  where
    e = S.filter (\e -> S.member (source e) s && S.member (target e) s) $ transition b
    f = S.intersection s $ final b

isThereOrdinary :: Buchi Event LTLState -> Bool
isThereOrdinary = S.foldr ((||) . isOrdinary . label) False . transition
  where
    isOrdinary evt = termination evt == Ordinary && foldr ((&&) . isOrdinary) True (refine evt)

writeBuchiInDot :: (Show a, Show s, Ord a, Ord s) => String -> Buchi a s -> IO ()
writeBuchiInDot str b = do
  let content = unlines . fmap ("  " ++) $ concat [["label = " `mappend` show str `mappend` ";", "", "//node define"], nodes, finalnodes, ["","//edge define"], es, initialnode]
  config <- readFile "images/.dotconfig"
  writeFile (concat ["images/", str, ".dot"]) $ concat [takeWhile (/= '}') config, content, "}"]
  rawSystem "dot" ["-Tpng", "-o", "images/" `mappend` str `mappend` ".png", "images/" `mappend` str `mappend` ".dot"]
  return ()
  where
    vs = S.toList $ states b
    m = M.fromList $ zip vs [0..]
    nodes = (\v -> concat [show (m M.! v), " [label = ", show $ show v, "];"]) <$> vs \\ S.toList (final b)
    finalnodes = (\v -> concat [show (m M.! v), " [shape = doublecircle, label = ", show $ show v, "];"]) <$> S.toList (final b)
    es = (\e -> concat [show $ m M.! source e, " -> ", show $ m M.! target e, " [label = ", show $ label e,"];"]) <$> S.toList (transition b)
    initialnode = case S.size (initial b) of
      0 -> []
      1 -> ["","{rank = min; " `mappend` show (m M.! S.findMin (initial b)) `mappend` ";}"]

test :: EventbMac -> IO ()
test mac = modelCheck mac testltl

testltl :: LTL AP
testltl = future (LAP (AExp (var "n") `Eq` AExp (AInt 1)))

-- followings are test ltl
-- response means that whenever p occurs then q will occur in the future
response :: AP -> AP -> LTL AP
response p q = global (LAP p `implication` future (LAP q))

-- absence means that if p will occur in the future then q wll not occur until p occur
absence :: AP -> AP -> LTL AP
absence p q = future (LAP p) `implication` (Eventb.LTL.LTL.Not (LAP q) `U` LAP p)

betweenAbsence :: AP -> AP -> AP -> LTL AP
betweenAbsence p q r = global ((LAP q `LAnd` Eventb.LTL.LTL.Not (LAP r) `LAnd` future (LAP r)) `implication` Eventb.LTL.LTL.Not (LAP p) `U` LAP r)

-- existence means that p will occur between occuring of q and r
existence :: AP -> AP -> AP -> LTL AP
existence p q r = global ((LAP q `LAnd` Eventb.LTL.LTL.Not (LAP r)) `implication` (Eventb.LTL.LTL.Not (LAP r) `weakUntil` (LAP p `LAnd` Eventb.LTL.LTL.Not (LAP r))))


-- precedence means that p will not occur until q occur
globallyPrecedence :: AP -> AP -> LTL AP
globallyPrecedence p q = Eventb.LTL.LTL.Not (LAP p) `weakUntil` LAP q

afterPrecedence :: AP -> AP -> AP -> LTL AP
afterPrecedence p q r = global (Eventb.LTL.LTL.Not (LAP q)) `LOr` future (LAP q `LAnd` (Eventb.LTL.LTL.Not (LAP p) `weakUntil` LAP r))

-- universality means that p always occur
globallyExistence :: AP -> LTL AP
globallyExistence p = future (LAP p)

betweenExistence :: AP -> AP -> AP -> LTL AP
betweenExistence p q r = global ((LAP q `LAnd` Eventb.LTL.LTL.Not (LAP r)) `implication` (Eventb.LTL.LTL.Not (LAP r) `weakUntil` (LAP p `LAnd` Eventb.LTL.LTL.Not (LAP r))))

testModelChecker :: EventbMac -> LTL AP -> IO ()
testModelChecker mac ltl = do
    let mac' = completeEvent mac
    (g,initv) <- makeLTLGraph mac' ltl
    putStrLn "model checking..."
    let b = optimizeBuchi $ intersectionBetweenGraphAndLTL (events mac') g initv (Eventb.LTL.LTL.Not ltl)
    case runReader (sccWithFinalAndOrdinary . stronglyConnComp $ buchiToGraph b) b of
      []   -> putStrLn "result: true"
      sccs -> do
        putStrLn "result: possible false"
        putStrLn "following automata possibly have ErrorPaths"
        let b_name = macname mac' `mappend` "_" `mappend` show (Eventb.LTL.LTL.Not ltl)
        -- writeBuchiInDot (rename b_name) b
        -- putStrLn $ "write a complete buchi automaton: " `mappend` b_name
        let b_ltl = ltlToBuchi (Eventb.LTL.LTL.Not ltl)
        writeBuchiInDot (rename . show $ Eventb.LTL.LTL.Not ltl) b_ltl
        putStrLn $ "write a ltl automaton: " `mappend` show (Eventb.LTL.LTL.Not ltl)
        mapM_ (\(scc,i) -> do
          let b_name = concat [macname mac', "_", show (Eventb.LTL.LTL.Not ltl), "_", show i]
          writeBuchiInDot (rename b_name) scc
          putStrLn $ "write a scc: " `mappend` b_name)
          $ zip sccs [0..]


-- data Vertex = V {cond :: Pred, enables :: [Event], props :: S.Set Pred}
-- type Vertices = [Vertex]
-- data Edge = Edge {source :: Vertex, target :: Vertex, label :: Event, wp :: WP}
-- type Edges = [Edge]
--
-- makeVertex :: (Pred, S.Set Pred) -> ReaderT [Event] IO Vertex
-- makeVertex (p, ps) = do
--   p' <- lift $ minimizePred p
-- --  let p' = p
--   evts <- ask
--   enableEvts <- lift $ filterM (fmap not . isUnsatisfiable . And p . mconcat . grd) evts
--   return V{cond = p', enables = enableEvts, props = ps}
--
-- makeVertices :: Inv -> [Pred] -> ReaderT [Event] IO [Vertex]
-- makeVertices inv ps = do
--   let v = foldr (\p acc -> fmap (And p A.*** S.insert p) acc `mappend` fmap (A.first $ And (Not p)) acc) [(inv,S.empty)] ps
--   vOfSat <- lift $ mapConcurrently (fmap not . isUnsatisfiable . fst) v
--   mapM (makeVertex . fst) . filter snd $ zip v vOfSat
