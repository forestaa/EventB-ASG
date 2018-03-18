{-# LANGUAGE MonadComprehensions #-}

module Eventb.LTL.LTL
    ( LTL (..)
    , ltlToBuchi
    , future
    , global
    , implication
    , weakUntil
    , membersInLTL
    ) where

import           Data.List
import qualified Eventb.LTL.Buchi as B
import           Eventb.LTL.Type
import qualified MySet            as S


data LTL a = Top | Bottom | LAP a | Not (LTL a) | LAnd (LTL a) (LTL a) | LOr (LTL a) (LTL a) | X (LTL a) | U (LTL a) (LTL a)
future :: LTL a -> LTL a
future = U Top
global :: LTL a -> LTL a
global = Not . future . Not
implication :: LTL a -> LTL a -> LTL a
implication = LOr . Not
weakUntil :: LTL a -> LTL a -> LTL a
weakUntil p q = p `U` (q `LOr` global p)

instance Show a => Show (LTL a) where
  show (Not (Top `U` Not ltl)) = concat ["G(", show ltl, ")"]
  show (Top `U` ltl) = concat ["F(",show ltl, ")"]
  show Top = "Top"
  show Bottom = "Bottom"
  show (LAP p) = show p
  show (Not ltl) = "not" `mappend` show ltl
  show (ltl1 `LAnd` ltl2) = concat ["(", show ltl1, "&", show ltl2, ")"]
  show (ltl1 `LOr` ltl2)  = concat ["(", show ltl1, "or", show ltl2, ")"]
  show (X ltl) = concat ["X(", show ltl, ")"]
  show (ltl1 `U` ltl2) = concat ["(", show ltl1, ")U(", show ltl2, ")"]

instance Eq a => Eq (LTL a) where
  Top == Top = True
  Bottom == Bottom = True
  LAP p == LAP q = p == q
  Not (Not p) == q = p == q
  p == Not (Not q) = p == q
  Not p == Not q = p == q
  (p `LAnd` p') == (q `LAnd` q') = p == q && p' == q'
  (p `LOr` p') == (q `LOr` q') = p == q && p' == q'
  X p == X q = p == q
  (p `U` p') == (q `U` q') = p == q && p' == q'
  _ == _ = False

instance Ord a => Ord (LTL a) where
  Top `compare` Top = EQ
  Bottom `compare` Top = GT
  Bottom `compare` Bottom = EQ
  LAP _ `compare` Top = GT
  LAP _ `compare` Bottom = GT
  LAP p `compare` LAP q = p `compare` q
  Not (Not p) `compare` q = p `compare` q
  p `compare` Not (Not q) = p `compare` q
  Not _ `compare` Top = GT
  Not _ `compare` Bottom = GT
  Not _ `compare` LAP _ = GT
  Not p `compare` Not q = p `compare` q
  LAnd _ _ `compare` Top = GT
  LAnd _ _ `compare` Bottom = GT
  LAnd _ _ `compare` LAP _ = GT
  LAnd _ _ `compare` Not _ = GT
  LAnd ltl1 ltl1' `compare` LAnd ltl2 ltl2'
    | ltl1 == ltl2 = ltl1' `compare` ltl2'
    | otherwise   = ltl1 `compare` ltl2
  LOr _ _ `compare` Top = GT
  LOr _ _ `compare` Bottom = GT
  LOr _ _ `compare` LAP _ = GT
  LOr _ _ `compare` Not _ = GT
  LOr _ _ `compare` LAnd _ _ = GT
  LOr ltl1 ltl1' `compare` LOr ltl2 ltl2'
    | ltl1 == ltl2 = ltl1' `compare` ltl2'
    | otherwise   = ltl1 `compare` ltl2
  X _ `compare` Top = GT
  X _ `compare` Bottom = GT
  X _ `compare` LAP _ = GT
  X _ `compare` Not _ = GT
  X _ `compare` LAnd _ _ = GT
  X _ `compare` LOr _ _ = GT
  X p `compare` X q = p `compare` q
  U _ _ `compare` Top = GT
  U _ _ `compare` Bottom = GT
  U _ _ `compare` LAP _ = GT
  U _ _ `compare` Not _ = GT
  U _ _ `compare` LAnd _ _ = GT
  U _ _ `compare` LOr _ _ = GT
  U _ _ `compare` X _ = GT
  U ltl1 ltl1' `compare` U ltl2 ltl2'
    | ltl1 == ltl2 = ltl1' `compare` ltl2'
    | otherwise = ltl1 `compare` ltl2
  _ `compare` _ = LT

data PosB s  = T | F | BAP s | BAnd (PosB s) (PosB s) | BOr (PosB s) (PosB s) deriving (Eq,Ord)

instance Show s => Show (PosB s) where
  show T              = "True"
  show F              = "False"
  show (BAP p)        = show p
  show (s1 `BAnd` s2) = concat ["(", show s1, " and ", show s2, ")"]
  show (s1 `BOr` s2)  = concat ["(", show s1, " or ", show s2, ")"]

type AEdge a s = (s,PosB s,a)
type AEdges a s = S.Set (AEdge a s)
data Alternating a s = Alt {alpha :: Alpha a, states :: States s, initial :: s, transition :: AEdges a s, final :: States s}

instance (Show a, Show s, Ord a, Ord s) => Show (Alternating a s) where
  show a = concat ["Alt\n alpha = ", show (alpha a), "\n S = ", show (states a), "\n s0 = ", show (initial a), "\n edges = ", show (transition a), "\n F = ", show (final a)]


ltlToBuchi :: Ord a => LTL a -> B.Buchi (S.Set a) (States (LTL a), States (LTL a))
ltlToBuchi = B.optimizeBuchi . altToBuchi . optimizeAlt . ltlToAlt

membersInPosB :: Ord s => PosB s -> S.Set s
membersInPosB T             = S.empty
membersInPosB F             = S.empty
membersInPosB (BAP p)       = S.singleton p
membersInPosB (p `BAnd` p') = membersInPosB p `S.union` membersInPosB p'
membersInPosB (p `BOr` p')  = membersInPosB p `S.union` membersInPosB p'

altToBuchi :: (Ord a, Ord s) => Alternating a s -> B.Buchi a (States s, States s)
altToBuchi a = B.Buchi (alpha a) s s0 edge f
  where
    directproduct s1 s2 = (,) <$> s1 <*> s2
    power = S.powerset $ states a
    s = directproduct power power
    s0 = S.singleton (S.singleton $ initial a, S.empty)
    f = directproduct (S.singleton S.empty) power
    edge = S.concat $ transOfAtoB power (final a) (transition a) <$> s <*> alpha a

transOfAtoB :: (Ord a, Ord s) => S.Set (States s) -> States s -> AEdges a s -> (States s, States s) -> a -> Edges a (States s, States s)
transOfAtoB power f edgeset (u,v) a
  | u == S.empty = [Edge (u,v) (u',v') a | y <- power, y `satisfy` p v, let u' = y S.\\ f, let v' = y `S.intersection` f]
  | otherwise    = [Edge (u,v) (u',v') a | x <- power, y <- power, x `satisfy` p u, y `satisfy` p v, let u' = x S.\\ f, let v' = y `S.union` (x `S.intersection` f)]
  where
    p x = S.foldr BAnd T . S.map (\(_,p,_) -> p) . S.filter (\(t,_,b) -> S.member t x && (a == b)) $ edgeset

satisfy :: Ord s => States s -> PosB s -> Bool
satisfy _ T             = True
satisfy _ F             = False
satisfy s (BAP p)       = S.member p s
satisfy s (p `BAnd` p') = satisfy s p && satisfy s p'
satisfy s (p `BOr` p')  = satisfy s p || satisfy s p'

ltlToAlt :: Ord a => LTL a -> Alternating (S.Set a) (LTL a)
ltlToAlt ltl = Alt a s s0 edge f
  where
    prop = membersInLTL ltl
    a = S.powerset prop
    s = subAndneg ltl
    s0 = ltl
    f = S.filter p s
    p (Not(U _ _)) = True
    p _            = False
    edge = (\fml s -> (fml, transOfLtoA fml s, s)) <$> s <*> a

transOfLtoA :: Ord a => LTL a -> States a -> PosB (LTL a)
transOfLtoA Top s = T
transOfLtoA Bottom s = F
transOfLtoA (LAP p) s = if S.member p s then T else F
transOfLtoA (Not ltl) s = dual $ transOfLtoA ltl s
transOfLtoA (ltl1 `LAnd` ltl2) s
  | posb1 == F || posb2 == F = F
  | posb1 == T = posb2
  | posb2 == T = posb1
  | otherwise = posb1 `BAnd` posb2
  where
    posb1 = transOfLtoA ltl1 s
    posb2 = transOfLtoA ltl2 s
transOfLtoA (ltl1 `LOr` ltl2) s
  | posb1 == T || posb2 == T = T
  | posb1 == F = posb2
  | posb2 == F = posb1
  | otherwise = posb1 `BOr` posb2
  where
    posb1 = transOfLtoA ltl1 s
    posb2 = transOfLtoA ltl2 s
transOfLtoA (X ltl) s = BAP ltl
transOfLtoA (ltl1 `U` ltl2) s
  | posb2 == T = T
  | posb1 == F = posb2
  | posb1 == T = posb2 `BOr` BAP (ltl1 `U` ltl2)
  | otherwise = posb2 `BOr` (posb1 `BAnd` BAP (ltl1 `U` ltl2))
  where
    posb1 = transOfLtoA ltl1 s
    posb2 = transOfLtoA ltl2 s

dual :: PosB (LTL a) -> PosB (LTL a)
dual T                  = F
dual F                  = T
dual (BAP (Not p))      = BAP p
dual (BAP p)            = BAP (Not p)
dual (ltl1 `BAnd` ltl2) = dual ltl1 `BOr` dual ltl2
dual (ltl1 `BOr` ltl2)  = dual ltl1 `BAnd` dual ltl2

membersInLTL :: Ord a => LTL a -> S.Set a
membersInLTL Top = S.empty
membersInLTL Bottom = S.empty
membersInLTL (LAP p) = S.singleton p
membersInLTL (Not ltl) = membersInLTL ltl
membersInLTL (ltl1 `LAnd` ltl2) = membersInLTL ltl1 `S.union` membersInLTL ltl2
membersInLTL (ltl1 `LOr` ltl2) = membersInLTL ltl1 `S.union` membersInLTL ltl2
membersInLTL (X ltl) = membersInLTL ltl
membersInLTL (ltl1 `U` ltl2) = membersInLTL ltl1 `S.union` membersInLTL ltl2

subAndneg :: Ord a => LTL a -> S.Set (LTL a)
subAndneg Top = S.fromList [Top,Bottom]
subAndneg Bottom = S.fromList [Top,Bottom]
subAndneg (LAP p) = S.fromList [LAP p, Not (LAP p)]
subAndneg (Not (Not ltl)) = subAndneg ltl
subAndneg (Not ltl) = S.fromList [ltl, Not ltl] `S.union` subAndneg ltl
subAndneg (ltl1 `LAnd` ltl2) = S.fromList [ltl1 `LAnd` ltl2, Not (ltl1 `LAnd` ltl2)] `S.union` subAndneg ltl1 `S.union` subAndneg ltl2
subAndneg (ltl1 `LOr` ltl2) = S.fromList [ltl1 `LOr` ltl2, Not (ltl1 `LOr` ltl2)] `S.union` subAndneg ltl1 `S.union` subAndneg ltl2
subAndneg (X ltl) = S.fromList [X ltl, Not (X ltl)] `S.union` subAndneg ltl
subAndneg (ltl1 `U` ltl2) = S.fromList [ltl1 `U` ltl2, Not (ltl1 `U` ltl2)] `S.union` subAndneg ltl1 `S.union` subAndneg ltl2

optimizeAlt :: (Ord a, Ord s) => Alternating a s -> Alternating a s
optimizeAlt a = Alt (alpha a) s (initial a) edges f
  where
    reach = reachablestates (transition a) (S.empty, S.singleton $ initial a)
    s = reach `S.intersection` states a
    edges = S.filter (\(fml,_,_) -> S.member fml reach) $ transition a
    f = reach `S.intersection` final a

reachablestates :: (Ord a, Ord s) => AEdges a s -> (States s,States s) -> States s
reachablestates edges (reached,search)
  | S.null search = reached
  | otherwise     = reachablestates edges (newreached, newsearch)
  where
    newreached = reached `S.union` search
    newsearch = reachable edges search S.\\ newreached

reachable :: (Ord a, Ord s) => AEdges a s -> States s -> States s
reachable edges s = S.filter (\(fml,_,_) -> S.member fml s) edges >>= \(_,fml,_) -> membersInPosB fml
