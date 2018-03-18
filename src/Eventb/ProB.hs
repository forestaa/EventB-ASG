module Eventb.ProB where

import           Control.Arrow
import           Control.Concurrent
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.List
import           Data.Maybe
import           Eventb
import           Eventb.Graph
import qualified MySet                as S
import           System.Exit
import           System.IO
import           System.Process
import           System.Random


proB :: FilePath
proB = "C:\\Users\\tdaic\\Desktop\\honiden\\ProB\\"

-- usingProB :: L.LTL AP -> ReaderT FilePath IO Bool
-- usingProB ltl = do
--   mac <- ask
--   out <- lift $ readProcess (proB `mappend` "probcli") ["-p","MAXINT","10","-ltlformula",show ltl,mac] ""
--   lift $ putStrLn out
--   return . elem "LTL Formula TRUE." . lines $ out
--
-- testProB :: EventbMac -> L.LTL AP -> IO Bool
-- testProB mac ltl = runReaderT (usingProB ltl) $ proB `mappend` "Examples\\Cars\\" `mappend` macname mac `mappend` "_mch.eventb"

-- testProB :: EventbMac -> [L.LTL AP] -> IO [(L.LTL AP,Bool)]
-- testProB mac ps = do
--   let macpath = proB `mappend` "Examples\\Cars\\" `mappend` macname mac `mappend` "_mch.eventb"
--   b <- mapConcurrently (flip runReaderT macpath . usingProB) ps
--   return $ zip ps b

doesGoThrough :: Edge -> ReaderT FilePath IO Bool
doesGoThrough e = do
  mac <- ask
  lift . putStrLn $ show (source e) `mappend` " [" `mappend` label e `mappend` "] " `mappend` show (target e)
  let ltl = "G(not(" `mappend` show (cond $ source e) `mappend` "&[" `mappend` label e `mappend` "]&X(" `mappend` show (cond $ target e) `mappend` ")))"
  out <- lift $ readProcess (proB `mappend` "probcli") ["-p", "MAXINT", "10","-ltlformula",ltl,mac] ""
  lift . putStrLn $ out
  return . elem "Formula FALSE." . lines $ out  -- "Formula False." means that there is a path through edge from source to target occuring event

searchPossibleEdge :: Edges -> ReaderT FilePath IO Edges
searchPossibleEdge = filterM doesGoThrough


-- doesGoThrough' :: Int -> Edge -> ReaderT FilePath IO Bool
-- doesGoThrough' d e = do
--   mac <- ask
--   lift . putStrLn $ show (source e) `mappend` " [" `mappend` name (label e) `mappend` "] " `mappend` show (target e)
--   let ltl = "G(not(" `mappend` show (cond $ source e) `mappend` "&[" `mappend` name (label e) `mappend` "]&X(" `mappend` show (cond $ target e) `mappend` ")))"
--   out <- lift $ readProcess (proB `mappend` "probcli") ["-ltlformula",ltl,mac] ""
--   lift . putStrLn $ out
--   return . elem "Formula FALSE." . lines $ out  -- "Formula False." means that there is a path through edge from source to target occuring event
--
-- searchPossibleEdge' :: Int -> Edges -> ReaderT FilePath IO Edges
-- searchPossibleEdge' = filterM . doesGoThrough'


filterUniqueEdges :: [Edges] -> [Edges]
filterUniqueEdges ess = fmap (\es -> filter (`S.notMember` (S.fromList . concat $ delete es ess)) es) ess

testEdges :: EventbMac -> IO ()
testEdges mac = do
  let mac' = completeEvent mac
  g <- makeEventGraph mac'
  let ds = [1..4]
      macpath d = concat [proB, "Examples\\Cars'\\", macname mac', "_d=", show d,"_mch.eventb"]
  es <- mapM (runReaderT (searchPossibleEdge (edges g)) . macpath) ds
  let uniqueEdges = filterUniqueEdges es
      datalog = (unlines . fmap show $ zip ds es) `mappend` show (zip ds (fmap length es)) `mappend` "\n" `mappend`show (zip ds uniqueEdges)
  writeFile "edgesAccordingConstant.log" datalog

removeEdgeUsingProB :: String -> Graph -> IO Graph
removeEdgeUsingProB macName g = do
  let macpath = proB `mappend` "Examples\\Cars\\" `mappend` macName `mappend` "_mch.eventb"
  es <- runReaderT (searchPossibleEdge (edges g)) macpath
  return $ g {edges = es}


showRemoveEdges :: Edges -> IO ()
showRemoveEdges = mapM_ (\e -> do
  putStrLn $ label e `mappend` " is not occured where"
  putStrLn $ ' ': show ({-cond $ -}source e)
  putStrLn " to"
  putStrLn $ ' ' : show ({-cond $ -}target e)
  )

-- test :: EventbMac -> IO ()
-- test mac = do
--   g <- makeGraph mac (mconcat . grd <$> events mac)
--   initv <- initVertex (initenv mac) (vertices g)
--   writeGraph (macname mac `mappend` "0") g initv
--   let g' = deleteUnreachableState initv g
--   writeGraph (macname mac `mappend` "1") g' initv
--   let macpath = proB `mappend` "Examples\\Cars\\" `mappend` macname mac `mappend` "_mch.eventb"
--   es <- runReaderT (searchPossibleEdge (edges g')) macpath
--   --es' <- runReaderT (searchPossibleEdge' (snd g')) macpath
--   writeGraph (macname mac `mappend` "2") (Graph (vertices g') es) initv
--   putStrLn "-------------------------------------"
--   showRemoveEdges (edges g' \\ es)
  --print $ es \\ es'

testForRandomSeqOfEvents :: EventbMac -> Graph -> Vertex -> Graph -> Vertex -> IO ()
testForRandomSeqOfEvents mac g initv g' initv' = do
  randomseq <- take 100 <$> makeRandomSeqOfEvents mac
  res <- catMaybes <$> mapM testseq randomseq
  putStrLn "test 100 sequences of events."
  putStrLn "The number of not existing seqences of events in Machine is"
  print $ length res
  putStrLn "In it, the number of not existing sequence of events in graph is"
  print $ (length . filter (not . fst) &&& length . filter (not . snd)) res
  where
    testseq evts = do
      c <- seqOfEventsCheckByProB' mac evts
      case c of
        Just False -> return . Just $ (isThereSuchPath g initv &&& isThereSuchPath g' initv') evts
        _          -> return Nothing

isThereSuchPath :: Graph -> Vertex -> [EventName] -> Bool
isThereSuchPath g initv path = evalState (runReaderT (isThereSuchPath' path) (edges g)) [initv]

isThereSuchPath' :: [EventName] -> ReaderT Edges (State [Vertex]) Bool
isThereSuchPath' [] = return True
isThereSuchPath' (evt:evts) = do
  vs <- get
  es <- ask
  let next = vs >>= \v -> fmap target (filter (\evt' -> source evt' == v && label evt' == evt) es)
  case next of
    [] -> return False
    _ -> do
      put next
      isThereSuchPath' evts

makeSeqOfEvents :: [Int] -> [Int] -> [Int] -> Reader EventbMac [[EventName]]
makeSeqOfEvents (l:ls) (i:is) rs = do
  mac <- ask
  (:) (initial5Events !! i `mappend` fmap ((name <$> events mac) !!) curr) <$> makeSeqOfEvents ls is rest
  where
    (curr,rest) = splitAt l rs

makeRandomSeqOfEvents :: EventbMac -> IO [[EventName]]
makeRandomSeqOfEvents mac = do
  gen1 <- newStdGen
  gen2 <- newStdGen
  gen3 <- newStdGen
  return $ runReader (makeSeqOfEvents (randomRs (1,5) gen1) (randomRs (0,13) gen2) (randomRs (0,7) gen3)) mac

seqOfEventsCheckByProB :: EventbMac -> [EventName] -> IO Bool
seqOfEventsCheckByProB mac evts = do
  print evts
  let ltl = seqOfEventsToProB evts
  out <- readProcess (proB `mappend` "probcli") ["-p", "MAXINT", "10","-ltlformula",ltl,proB `mappend` "Examples\\Cars\\" `mappend` macname mac `mappend` "_mch.eventb"] ""
  return . elem "Formula FALSE." . lines $ out

seqOfEventsCheckByProB' :: EventbMac -> [EventName] -> IO (Maybe Bool)
seqOfEventsCheckByProB' mac evts = do
  print evts
  let ltl = seqOfEventsToProB evts
  (_,Just out,_,ph) <- createProcess $ (proc (proB `mappend` "probcli") ["-ltlformula",ltl,proB `mappend` "Examples\\Cars\\" `mappend` macname mac `mappend` "_mch.eventb"]) {std_out = CreatePipe}
  threadDelay (3*10^6)
  code <- getProcessExitCode ph
  case code of
    Nothing              -> terminateProcess ph >> return Nothing
    Just ExitSuccess     -> do
      res <- hGetContents out
      return . Just . elem "Formula FALSE." . lines $ res
    Just (ExitFailure _) -> return Nothing

seqOfEventsToProB :: [EventName] -> String
seqOfEventsToProB evts = concat ["not(",intercalate "&" $ evalState (f $ fmap (\evt -> concat ["[", evt, "]"]) evts) 0,")"]
  where
    f [] = return [] :: State Int [String]
    f (x:xs) = do
      i <- get
      put (i+1)
      (:) (replicate i 'X' `mappend` x) <$> f xs

initial5Events :: [[EventName]]
initial5Events = [ ["ML_tl_green","ML_out_1","ML_out_1","ML_out_1","ML_out_1"]
                 , ["ML_tl_green","ML_out_1","ML_out_1","ML_out_1","ML_out_2"]
                 , ["ML_tl_green","ML_out_1","ML_out_1","ML_out_1","IL_in"]
                 , ["ML_tl_green","ML_out_1","ML_out_1","ML_out_2","IL_in"]
                 , ["ML_tl_green","ML_out_1","ML_out_1","IL_in","ML_out_1"]
                 , ["ML_tl_green","ML_out_1","ML_out_1","IL_in","ML_out_2"]
                 , ["ML_tl_green","ML_out_1","ML_out_1","IL_in","IL_in"]
                 , ["ML_tl_green","ML_out_1","ML_out_2","IL_in","IL_in"]
                 , ["ML_tl_green","ML_out_1","IL_in","ML_out_1","ML_out_1"]
                 , ["ML_tl_green","ML_out_1","IL_in","ML_out_1","ML_out_2"]
                 , ["ML_tl_green","ML_out_1","IL_in","ML_out_1","IL_in"]
                 , ["ML_tl_green","ML_out_1","IL_in","ML_out_2","IL_in"]
                 , ["ML_tl_green","ML_out_1","IL_in","IL_tl_green","IL_out_1"]
                 , ["ML_tl_green","ML_out_2","IL_in","IL_tl_green","IL_out_2"]
                 ]

nondeterministicEdges :: Graph -> [(Vertex,Int)]
nondeterministicEdges g = zip (vertices g) nondet
  where
    nondet = (\v -> flip evalState S.empty . count . filter ((==) v . source) $ edges g) <$> vertices g
    count [] = return 0 :: State (S.Set String) Int
    count (e:es) = do
      s <- get
      if label e `S.member` s
        then (+) 1 <$> count es
        else do
          put $ S.insert (label e) s
          count es
