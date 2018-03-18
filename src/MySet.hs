{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MySet where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import qualified Data.Set.Monad      as S

newtype Set a = Set {get :: S.Set a}
  deriving (Alternative, Monad, Functor, MonadPlus, Applicative, Foldable, Eq, Ord, Read, Monoid)

instance (Show a, Ord a) => Show (Set a) where
  show a | MySet.null a    = "empty"
         | otherwise = '{' : mappend (init . tail . show . toList $ a) "}"

infixr 9 \\
(\\) :: Ord a => Set a -> Set a -> Set a
x \\ y = Set $ get x S.\\ get y

null :: Ord a => Set a -> Bool
null = S.null . get

size :: Ord a => Set a -> Int
size = S.size . get

member :: Ord a => a -> Set a -> Bool
member a s = S.member a $ get s

notMember :: Ord a => a -> Set a -> Bool
notMember = (not .) . member

isSubsetOf :: Ord a => Set a -> Set a -> Bool
isSubsetOf x y = get x `S.isSubsetOf` get y

empty :: Ord a => Set a
empty = Set S.empty

singleton :: Ord a => a -> Set a
singleton = Set . S.singleton

insert :: Ord a => a -> Set a -> Set a
insert x = Set . S.insert x . get

delete :: Ord a => a -> Set a -> Set a
delete x = Set . S.delete x . get

union :: Ord a => Set a -> Set a -> Set a
union x y = Set $ get x `S.union` get y

unions :: Ord a => [Set a] -> Set a
unions = Prelude.foldr union MySet.empty

concat :: Ord a => Set (Set a) -> Set a
concat = MySet.foldr union MySet.empty

intersection :: Ord a => Set a -> Set a -> Set a
intersection x y = Set $ get x `S.intersection` get y

filter :: Ord a => (a -> Bool) -> Set a -> Set a
filter p = Set . S.filter p . get

partition :: Ord a => (a -> Bool) -> Set a -> (Set a, Set a)
partition p = (Set *** Set) . S.partition p . get

map :: (Ord a, Ord b) => (a -> b) -> Set a -> Set b
map f = Set . S.map f . get

foldr :: (Ord a, Ord b) => (a -> b -> b) -> b -> Set a -> b
foldr f z = S.foldr f z . get

deleteMin :: Ord a => Set a -> Set a
deleteMin = Set . S.deleteMin . get

findMin :: Ord a => Set a -> a
findMin = S.findMin . get

toList :: Ord a => Set a -> [a]
toList = S.toList . get

fromList :: Ord a => [a] -> Set a
fromList = Set . S.fromList


-- the followings are my functions.
powerset :: Ord a => Set a -> Set (Set a)
powerset = MySet.foldr (\x y -> y `MySet.union` MySet.map (MySet.insert x) y) (MySet.singleton MySet.empty)

satisfyingElement :: Ord a => (a -> Bool) -> Set a -> Maybe a
satisfyingElement p = MySet.foldr f Nothing
  where
    f _ (Just a) = Just a
    f a Nothing  = if p a then Just a else Nothing

disjointunion :: Ord a => [Set a] -> Set (Int,a)
disjointunion = MySet.unions . zipWith f [1..]
  where
    f i = MySet.map (\s -> (i,s))

directproduct :: Ord a => [Set a] -> Set [a]
directproduct = MySet.fromList . Prelude.foldr ((<*>) . fmap (:) . MySet.toList) [[]]
