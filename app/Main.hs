module Main where

-- import           Control.Monad
import           Eventb
import qualified Eventb.Graph   as G
-- import           Eventb.LTL.LTL
-- import qualified Eventb.ModelCheck as M
-- import qualified Eventb.Scenario   as S
import           Criterion
import           Criterion.Main

main :: IO ()
main = do
  g <- G.makeEventGraph mac0
  g' <- G.makeEventGraphKai (mac0,g) mac1
  g'' <- G.makeEventGraphKai (mac1,g') mac2'
  putStrLn "Done"
  -- defaultMain [ bench "refinement" . nfIO $ G.makeEventGraphKai (mac0, g) mac1 ]
