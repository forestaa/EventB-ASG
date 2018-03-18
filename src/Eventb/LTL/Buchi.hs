{-# LANGUAGE MonadComprehensions #-}

module Eventb.LTL.Buchi
     ( Buchi (..)
--     , isempty
     , intersectionOfTwoBuchis
     , unionOfBuchis
     , intersectionOfBuchis
     , optimizeBuchi
     ) where


import           Control.Arrow
import           Control.Monad.Reader
import           Eventb.LTL.Type
import qualified MySet                as S

data Buchi a s = Buchi {alpha :: Alpha a, states :: States s, initial :: States s, transition :: Edges a s, final :: States s}

instance (Show a, Show s, Ord a, Ord s) => Show (Buchi a s) where
  show b = concat ["Buchi\n alpha = ", show (alpha b), "\n S = ", show (states b), "\n S0 = ", show (initial b), "\n edges = ", show (transition b), "\n F = ", show (final b)]

newtype Logger a s = Logger {runLogger :: (s,[a])} deriving Show

instance Eq s => Eq (Logger a s) where
  Logger (s,_) == Logger (s',_) = s == s'

instance Ord s => Ord (Logger a s) where
  Logger (s,_) `compare` Logger (s',_) = s `compare` s'

makeLogger :: s -> Logger a s
makeLogger s = Logger (s,[])

keeplog :: Logger a s -> (s,a) -> Logger a s
keeplog l (s,a) = Logger (s,(:) a . snd . runLogger $ l)

escapeLogger :: Logger a s -> s
escapeLogger = fst . runLogger

takelog :: Logger a s -> [a]
takelog = snd . runLogger
--
-- newtype ErrorPath a = ErrorPath {runErrorPath :: ([a],[a])}
--
-- instance Show (ErrorPath a) where
--   show e = case runErrorPath e of
--     (reach,lasso) ->

isempty :: (Show a, Ord a, Ord s) => Buchi a s -> IO ()
isempty b = case isnonempty b of
  Nothing -> putStrLn "result: true"
  Just (reach,lasso) -> do
    putStrLn "result: false"
    putStrLn $ concat ["errorpath: ", pathprint reach, " -> (", pathprint lasso, " -> )..."]
  where
    pathprint []     = ""
    pathprint [a]    = show a
    pathprint (a:as) = concat [show a, " -> ", pathprint as]

isnonempty :: (Ord a, Ord s) => Buchi a s -> Maybe ([a],[a])
isnonempty b = S.foldr g Nothing . final $ b
  where
    g _ (Just m) = Just m
    g f Nothing  = isLassoAndReachable (initial b) (transition b) f


isLassoAndReachable :: (Ord a,Ord s) => States s -> Edges a s -> s -> Maybe ([a],[a])
isLassoAndReachable s0 edges f =
  isLassoAndReachable' s0 edges f (S.empty, invtrans edges . makeLogger $ f)

isLassoAndReachable' :: (Ord a, Ord s) => States s -> Edges a s -> s -> (S.Set (Logger a s), S.Set (Logger a s)) -> Maybe ([a],[a])
isLassoAndReachable' initials edges f (reached, search)
  | lasso && reachable = (,) <$> s0log <*> flog
  | S.null search = Nothing
  | otherwise = isLassoAndReachable' initials edges f (newreached, newsearch)
  where
    lasso = S.foldr (\s acc -> acc || isLasso f s) False reached
    reachable = S.foldr (\s acc -> acc || isReachable initials s) False reached
    newreached = reached `S.union` search
    newsearch = (search >>= invtrans edges) S.\\ newreached
    flog = takelog <$> S.satisfyingElement (isLasso f) reached
    s0log = takelog <$> S.satisfyingElement (isReachable initials) reached

isLasso :: Ord s => s -> Logger a s -> Bool
isLasso s = (==) s . escapeLogger

isReachable :: Ord s => States s -> Logger a s -> Bool
isReachable initials = flip S.member initials . escapeLogger

invtrans :: (Ord a, Ord s) => S.Set (Edge a s) -> Logger a s -> S.Set (Logger a s)
invtrans edges l = S.map (keeplog l . f) . S.filter ((==) (escapeLogger l) . target) $ edges
  where
    f e  = (source e, label e)

-- We can make union of n Buchi automata.
unionOfBuchis :: (Ord a, Ord s) => [Buchi a s] -> Buchi a (Int,s)
unionOfBuchis list = Buchi a s s0 edges f
  where
    a = S.unions $ fmap alpha list
    s = S.disjointunion $ fmap states list
    s0 = S.disjointunion $ fmap initial list
    f = S.disjointunion $ fmap final list
    edges = S.unions . zipWith (\i edgeset -> S.map (\e -> Edge (i,source e) (i,target e) (label e)) edgeset) [1..] . fmap transition $ list

intersectionOfTwoBuchis :: (Ord a, Ord s, Ord s') => Buchi a s -> Buchi a s' -> Buchi a (s,s',Int)
intersectionOfTwoBuchis b b' = Buchi a s s0 edges f
  where
    directproduct s1 s2 s3 = (,,) <$> s1 <*> s2 <*> s3
    a = alpha b `S.union` alpha b'
    s = directproduct (states b) (states b') (S.fromList [1,2])
    s0 = directproduct (initial b) (initial b') (S.singleton 1)
    edges = s >>= intertransOfTwoBuchis a (final b) (final b') (transition b) (transition b')
    f = directproduct (final b) (states b') (S.singleton 1)

intertransOfTwoBuchis :: (Ord a, Ord s, Ord s') => Alpha a -> States s -> States s' -> Edges a s -> Edges a s' -> (s,s',Int) -> Edges a (s,s',Int)
intertransOfTwoBuchis alpha f1 f2 edge1 edge2 (s,t,i) =
  [ Edge (s,t,i) (s',t',j) a | a <- alpha, s' <- dest s a edge1, t' <- dest t a edge2]
  where
    dest src a = S.map target . S.filter (\e -> src == source e && a == label e)
    j | i == 1 && S.member s f1 = 2
      | i == 2 && S.member t f2 = 1
      | otherwise               = i

-- We can make intersecion of n Buchi automata. if n == 0, exception occurs.
intersectionOfBuchis :: (Ord a, Ord s) => [Buchi a s] -> Buchi a (Int,[s])
intersectionOfBuchis list = Buchi a s s0 e f
  where
    n  = length list
    a  = foldr (S.intersection . alpha) (S.unions . fmap alpha $ list) list
    s  = S.disjointunion . replicate n . S.directproduct . fmap states $ list
    s0 = S.disjointunion . replicate 1 . S.directproduct . fmap initial $ list
    f  = S.disjointunion . replicate 1 . S.directproduct . (:) (final . head $ list) . fmap states . tail $ list
    e  = S.concat . S.map (intertrans (fmap final list)) . S.filter p . S.directproduct . fmap transition $ list
    p = and . (\xs -> zipWith (==) xs (tail xs)) . fmap target

intertrans :: (Ord a, Ord s) => [States s] -> [Edge a s] -> S.Set (Edge a (Int,[s]))
intertrans fsetlist edgelist = S.fromList $ zipWith3 f fsetlist srclist [1..]
  where
    a = label $ head edgelist
    srclist = fmap source edgelist
    tarlist = fmap target edgelist
    f fset s i | i == length fsetlist = if S.member s fset
                                        then Edge (i,srclist) (1,tarlist) a
                                        else Edge (i,srclist) (i,tarlist) a
               | otherwise            = if S.member s fset
                                        then Edge (i,srclist) (i+1,tarlist) a
                                        else Edge (i,srclist) (i,tarlist) a

optimizeBuchi :: (Ord a, Ord s) => Buchi a s -> Buchi a s
optimizeBuchi b = Buchi (alpha b) s (initial b) edges f
  where
    reach = reachablestates (transition b) (S.empty, initial b)
    s = reach `S.intersection` states b
    edges = S.filter (\e -> S.member (source e) reach && S.member (target e) reach) $ transition b
    f = reach `S.intersection` final b

reachablestates :: (Ord a, Ord s) => Edges a s -> (States s, States s) -> States s
reachablestates edges (reached, search)
  | S.null search = reached
  | otherwise     = reachablestates edges (newreached, newsearch)
  where
    newreached = reached `S.union` search
    newsearch = reachable edges search S.\\ newreached

reachable :: (Ord a, Ord s) => Edges a s -> States s -> States s
reachable edges set = S.map target . S.filter (flip S.member set . source) $ edges
