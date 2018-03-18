module Eventb.LTL.Type where

import qualified MySet as S

type Alpha a = S.Set a
type States s = S.Set s
data Edge a s = Edge {source :: s, target :: s, label :: a} deriving (Show, Eq, Ord)
type Edges a s = S.Set (Edge a s)
