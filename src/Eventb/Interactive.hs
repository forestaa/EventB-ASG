module Eventb.Interactive where

import           Control.Arrow
import           Data.Map.Strict hiding (filter)
import           Data.Maybe
import           Eventb          hiding (execEvent)
import           System.IO

proB :: EventbMac -> IO ()
proB mac = do
  constenv <- initializeconsts mac
  let env = union constenv $ initenv mac
  interaction env

printEnv :: Env -> IO ()
printEnv env = mapM_ putStrLn $ foldrWithKey (\var value list -> concat [var, " = ", show value] : list) [] env

printEnableActions :: Env -> EventbMac -> IO ()
printEnableActions env mac = mapM_ putStrLn . filter ("" /=) . flip (uncurry (zipWith3 f)) [0..] . (fmap name &&& fmap (grdcheck env)) $ events mac
  where
    f str Prelude.True i  = concat [show i, ": ", str]
    f str Prelude.False i = []

interaction :: Env -> IO ()
interaction env = do
  printEnv env
  putStrLn "enable actions are followings"
  printEnableActions env mac0
  putStrLn "What do you execute action?"
  i <- getLine
  let event = events mac0 !! read i
      newenv = execEvent env event
  interaction newenv


evalAExp :: Env -> AExp -> Int
evalAExp env (AInt i)    = i
evalAExp env (AVar v)    = evalAExp env . fromJust . isAExp $ env ! v
evalAExp env (Add e1 e2) = evalAExp env e1 + evalAExp env e2
evalAExp env (Sub e1 e2) = evalAExp env e1 - evalAExp env e2
evalAExp env (Mul e1 e2) = evalAExp env e1 * evalAExp env e2
evalAExp env (Div e1 e2) = evalAExp env e1 `div` evalAExp env e2

evalValue :: Env -> Value -> Value
evalValue env (AExp a) = AExp . AInt $ evalAExp env a

evalBExp :: Env -> BExp -> Bool
evalBExp env T             = True
evalBExp env F             = False
evalBExp env (Eq v1 v2)    = evalValue env v1 == evalValue env v2
evalBExp env (Gt e1 e2)    = evalAExp env e1 > evalAExp env e2
evalBExp env (And e1 e2)   = evalBExp env e1 && evalBExp env e2
evalBExp env (Or e1 e2)    = evalBExp env e1 || evalBExp env e2
evalBExp env (Not e)       = not $ evalBExp env e
evalBExp env (Imply e1 e2) = not (evalBExp env e1) || evalBExp env e2

initializeconsts :: EventbMac -> IO Env
initializeconsts mac = do
  putStrLn "Initialize constants"
  let constants = sees mac >>= extract consts
  maplist <- mapM getVal constants
  let initenv = fromList $ zip constants maplist
  if axiomcheck mac initenv
    then return initenv
    else do
      putStrLn "violate some axioms"
      initializeconsts mac
  where
    getVal var = do
      putStr $ var `mappend` " = "
      hFlush stdout
      value <- readLn
      return . AExp . AInt $ value

extract :: (EventbCtx -> [a]) -> EventbCtx -> [a]
extract f = uncurry mappend . (f &&& ((=<<) (extract f) . extends))

axiomcheck :: EventbMac -> Env -> Bool
axiomcheck mac env = and . fmap (evalBExp env) $ sees mac >>= extract axiom

grdcheck :: Env -> Event -> Bool
grdcheck env event = and . fmap (evalBExp env) $ grd event

execEvent :: Env -> Event -> Env
execEvent env event = fmap (AExp . AInt . evalAExp env . fromJust . isAExp) (act event) `union` env
