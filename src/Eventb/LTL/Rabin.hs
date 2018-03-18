{-# LANGUAGE MonadComprehensions #-}

module Eventb.LTL.Rabin (complementOfBuchi) where

import           Control.Arrow
import qualified Control.Monad.State as St
import           Data.List
import qualified Eventb.LTL.Buchi    as B
import           Eventb.LTL.Type
import qualified MySet               as S

data Rabin a s = Rabin {alpha :: Alpha a, states :: States s, initial :: States s, transition :: S.Set (Edge a s), final :: S.Set (States s, States s)}

instance (Show a, Show s, Ord a, Ord s) => Show (Rabin a s) where
  show r = concat ["Rabin\n alpha = ", show (alpha r), "\n S = ", show (states r), "\n S0 = ", show (initial r), "\n edges = ", show (transition r), "\n F = ", show (final r)]


complementOfBuchi :: (Ord a, Ord s, Show s) => B.Buchi a s -> B.Buchi a (Int,[(Int,(Int,(Int,SafraTree s)))])
complementOfBuchi b = B.optimizeBuchi . rabinCompToBuchi . unionOfRabins . fmap (\s0 -> safraconstruction b{B.initial = S.singleton s0}) . S.toList . B.initial $ b


rabinCompToBuchi :: (Ord a, Ord s) => Rabin a s -> B.Buchi a (Int,[(Int,(Int,s))])
rabinCompToBuchi r = B.intersectionOfBuchis . fmap (\(l,u) -> rabinToBuchi r{final = S.fromList [(u,S.empty),(states r,l)]}) . S.toList . final $ r

rabinToBuchi :: (Ord a, Ord s) => Rabin a s -> B.Buchi a (Int,(Int,s))
rabinToBuchi r = B.unionOfBuchis . fmap (\rcond -> rabin1ToBuchi r{final = S.singleton rcond}) . S.toList . final $ r

rabin1ToBuchi :: (Ord a, Ord s) => Rabin a s -> B.Buchi a (Int,s)
rabin1ToBuchi r = B.Buchi (alpha r) s s0 edge f
  where
    (l,u) = S.findMin $ final r
    s = S.disjointunion [states r, states r S.\\ u]
    s0 = S.map (\s0 -> (1,s0)) $ initial r
    f = S.map (\s -> (2,s)) l
    edge = transition r >>= transRtoB u

transRtoB :: (Ord a, Ord s) => States s -> Edge a s -> S.Set (Edge a (Int,s))
transRtoB u Edge {source = s, target = s', label = a}
  | S.member s' u = S.fromList [Edge (1,s) (1,s') a]
  | S.member s u  = S.fromList [Edge (1,s) (1,s') a, Edge (1,s) (2,s') a]
  | otherwise     = S.fromList [Edge (1,s) (1,s') a, Edge (1,s) (2,s') a, Edge (2,s) (2,s') a]

unionOfRabins :: (Ord a, Ord s) => [Rabin a s] -> Rabin a (Int,s)
unionOfRabins list = Rabin a s s0 edges f
  where
    a = S.unions $ fmap alpha list
    s = S.disjointunion $ fmap states list
    s0 = S.disjointunion $ fmap initial list
    edges = S.unions . zipWith (\i edgeset -> S.map (\e -> Edge (i,source e) (i,target e) (label e)) edgeset) [1..] . fmap transition $ list
    f = S.unions . zipWith (\i s -> S.map (S.map ((,) i) *** S.map ((,) i)) s) [1..] . fmap final $ list



-- following is about safra construction
data Node s = Node { name        :: Int
                   , macrostates :: S.Set s
                   , mark        :: Bool } deriving (Show, Eq, Ord)

data SafraTree s = Empty
                 | TNode { node :: Node s
                         , sons :: [SafraTree s] }
                 deriving (Show, Eq, Ord)

tmap :: (Node a -> Node b) -> SafraTree a -> SafraTree b
tmap f Empty        = Empty
tmap f (TNode n ts) = TNode (f n) (fmap (tmap f) ts)


-- input: Buchi automaton with 1 initial state
safraconstruction :: (Ord a, Ord s) => B.Buchi a s -> Rabin a (SafraTree s)
safraconstruction b = Rabin (B.alpha b) treestates (S.singleton t0) edges f
  where
    (treestates,edges) = safraconstruction' (B.alpha b) (B.final b) (B.transition b) (S.empty, S.singleton (t0,S.fromList [2 .. 2 * S.size (B.states b)])) S.empty
    f = rabinconditionsOfSafra treestates
    t0 = TNode {node = Node 1 (B.initial b) False, sons = []}

safraconstruction' :: (Ord a, Ord s) => Alpha a -> States s -> Edges a s -> (S.Set (SafraTree s), S.Set (SafraTree s, S.Set Int)) -> Edges a (SafraTree s) -> (S.Set (SafraTree s), Edges a (SafraTree s))
safraconstruction' alphas f edges (reached, search) safraedges
  | S.null search = (reached, safraedges)
  | otherwise = safraconstruction' alphas f edges (newreached, newsearch) (safraedges `S.union` newedges)
  where
    newbe = [ (q,a, St.runState (step a $ return q) nonused) | (q,nonused) <- search, a <- alphas ]
    newedges = S.map (\(q,a,(q',_)) -> Edge q q' a) newbe
    newreached = reached `S.union` S.map fst search
    newsearch = S.filter (\(q,_) -> S.notMember q newreached) . S.map (\(_,_,t) -> t) $ newbe
    step a = (step6 =<<) . (step5 =<<) . fmap (step4 S.empty . step3 edges a) . (step2 f =<<) . fmap step1


step1 :: SafraTree s -> SafraTree s
step1 = tmap (\node -> node{mark = False})

step2 :: Ord s => States s -> SafraTree s -> St.State (States Int) (SafraTree s)
step2 f Empty = return Empty
step2 f t@(TNode n ts)
  | S.null m = foldr chain (return []) ts >>= \ts' -> return t{sons = ts'}
  | otherwise = do
      nonused <- St.get
      let newname = S.findMin nonused
      St.put $ newname `S.delete` nonused
      ts' <- foldr chain (return []) ts
      return t{sons = TNode (Node newname m False) [] : ts'}
  where
    m = macrostates n `S.intersection` f
    chain t s = do
      acc <- s
      t' <- step2 f t
      return $ t':acc

step3 :: (Eq a, Ord s) => Edges a s -> a -> SafraTree s -> SafraTree s
step3 edges a = tmap (\n -> n{macrostates = [ q | Edge {source = m, target = q, label = a'} <- edges, a == a', S.member m (macrostates n) ]})

step4 :: Ord s => States s -> SafraTree s -> SafraTree s
step4 _ Empty = Empty
step4 s t@(TNode n ts) = t{node = n{macrostates = m'},sons = zipWith step4 olders ts}
  where
    m' = macrostates n S.\\ s
    tail' ls = if null ls then [] else tail ls
    f = macrostates . node
    olders = foldr (\t acc -> (f t `S.union` head acc):acc) [s] . tail' $ ts

putsonsname :: [SafraTree s] -> St.State (States Int) ()
putsonsname [] = return ()
putsonsname (t:ts) = do
  nonused <- St.get
  St.put $ (name . node $ t) `S.insert` nonused
  putsonsname ts

step5 :: Ord s => SafraTree s -> St.State (States Int) (SafraTree s)
step5 Empty = return Empty
step5 t@(TNode n ts)
  | S.null . macrostates $ n = do
      nonused <- St.get
      St.put $ name n `S.insert` nonused
      putsonsname ts
      return Empty
  | otherwise = foldr chain (return []) ts >>= \ts' -> return t{sons = ts'}
  where
    chain t s = do
      acc <- s
      t' <- step5 t
      case t' of
        Empty -> return acc
        t''   -> return $ t'':acc

step6 :: Ord s => SafraTree s -> St.State (States Int) (SafraTree s)
step6 Empty = return Empty
step6 t@(TNode n ts)
  | macrostates n == sonlabels = putsonsname ts >> return t{node = n{mark = True}, sons = []}
  | otherwise = foldr chain (return []) ts >>= \ts' -> return t{sons = ts'}
  where
    sonlabels = foldr (S.union . macrostates . node) S.empty ts
    chain t s = do
      acc <- s
      t' <- step6 t
      return $ t':acc

rabinconditionsOfSafra :: Ord s => States (SafraTree s) -> S.Set (States (SafraTree s), States (SafraTree s))
rabinconditionsOfSafra trees = S.map (f &&& e) v
  where
    v = trees >>= nodesOfTree
    f node = S.filter (marked node) trees
    e node = S.filter (without node) trees

nodesOfTree :: SafraTree s -> S.Set Int
nodesOfTree Empty = S.empty
nodesOfTree (TNode n ts) = name n `S.insert` foldr (S.union . nodesOfTree) S.empty ts

marked :: Int -> SafraTree s -> Bool
marked _ Empty = False
marked i (TNode n ts)
  | name n == i = mark n
  | otherwise = foldr ((||) . marked i) False ts

without :: Int -> SafraTree s -> Bool
without _ Empty = True
without i (TNode n ts)
  | name n == i = False
  | otherwise = foldr ((&&) . without i) True ts
