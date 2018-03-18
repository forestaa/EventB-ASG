module Eventb.Dot where

import           Control.Monad.Reader
import           Data.List
import qualified Data.Map             as M
import           Eventb.Graph
import           System.Process

graphToDot :: String -> Graph -> Maybe Vertex -> Reader (M.Map Vertex Int) String
graphToDot s g initv = do
  nodes <- verticesToDot $ vertices g
  es <- edgesToDot $ edges g
  suffix <- initvToDot initv
  return . unlines . fmap ("  " ++) $ concat [["label = " `mappend` show s `mappend` ";","", "//node define"], nodes, ["","//edge define"], es, suffix]

verticesToDot :: Vertices -> Reader (M.Map Vertex Int) [String]
verticesToDot vs = (\intMap -> fmap (\v -> concat [show (intMap M.! v), " [label = ", show $ show v, "];"]) vs) <$> ask

edgesToDot :: Edges -> Reader (M.Map Vertex Int) [String]
edgesToDot es = (\intMap -> fmap (\e -> concat [show $ intMap M.! source e, " -> ", show $ intMap M.! target e, " [label = ", show $ show e,"];"]) es) <$> ask

initvToDot :: Maybe Vertex -> Reader (M.Map Vertex Int) [String]
initvToDot Nothing = return []
initvToDot (Just v) = (\intMap -> ["","{rank = min; " `mappend` show (intMap M.! v) `mappend` ";}"]) <$> ask

refinementGraphToDot :: RefinementGraph -> String
refinementGraphToDot (RefinementGraph _ concrete sim) = unlines content
  where
    intMap = M.fromList $ zip (vertices concrete) [1..]
    subGraphs = M.toList $ fmap (\vs -> Graph vs (filter (\e -> source e `elem` vs && target e `elem` vs) $ edges concrete)) sim
    refineEdges = edgesToDot $ edges concrete \\ foldr union [] (fmap (edges . snd) subGraphs)
    content = runReader (mappend <$> zipWithM subGraphToDot [1..] subGraphs <*> (fmap ("  " ++) <$> refineEdges)) intMap

subGraphToDot :: Int -> (AbstractVertex, Graph) -> Reader (M.Map ConcreteVertex Int) String
subGraphToDot i (v,g) = do
  content <- graphToDot (show $ enables v) g Nothing
  return $ unlines . fmap ("  " ++) . concat $ [["subgraph cluster_" `mappend` show i `mappend` " {"], lines content, ["}"]]

writeGraph :: String -> Graph -> Vertex -> IO ()
writeGraph str graph initv = writeGraphInternal str $ runReader (graphToDot str graph (Just initv)) . M.fromList $ zip (vertices graph) [1..]

writeRefinementGraph :: String -> RefinementGraph -> IO ()
writeRefinementGraph str refinementGraph = writeGraphInternal str $ refinementGraphToDot refinementGraph

writeGraphInternal :: String -> String -> IO ()
writeGraphInternal str content = do
  config <- readFile "images/.dotconfig"
  writeFile (concat ["images/",str,".dot"]) $ concat [takeWhile (/= '}') config, content, "}"]
  rawSystem "dot" ["-Tpng", "-o", "images/" `mappend` str `mappend` ".png", "images/" `mappend` str `mappend` ".dot"]
  return ()
