module Main where

import           Eventb
import qualified Eventb.Graph      as G
import qualified Eventb.ModelCheck as M
import qualified Eventb.Dot        as D

main :: IO ()
main = loop [test1,test2,test3,test4,test5,test6,test7,test8,test9,test10]
  where
    loop [] = return ()
    loop (t:ts) = do
      let ltl = t
      print ltl
      -- G.testProB mac2' ltl >>= print
      M.testModelChecker mac2 ltl
      loop ts

avar = [var "n",var "a",var "b",var "c"]
atar = [AInt 0,AInt 1,var "d",var "d" `Sub` AInt 1]
bvar = [var "ml_pass",var "il_pass"]
btar = [TRUE,FALSE]
cvar = [var "ml_tl",var "il_tl"]
ctar = [Red,Green]
allTestPred = (Gt <$> avar <*> atar) `mappend` (Eq <$> fmap AExp avar <*> fmap AExp atar) `mappend` (Eq <$> fmap BExp bvar <*> fmap BExp btar) `mappend` (Eq <$> fmap Color cvar <*> fmap Color ctar)

test1 = M.betweenAbsence (BExp (var "ml_pass") `Eq` BExp FALSE) (var "a" `Gt` AInt 0) (AExp (var "a") `Eq` AExp (AInt 0))
test2 = M.betweenAbsence (Color (var "ml_tl") `Eq` Color Green) (AExp (var "d") `Eq` AExp (var "n")) (var "d" `Gt` var "n")

test3 = M.globallyExistence (Color (var "il_tl") `Eq` Color Green)
test4 = M.betweenExistence (BExp (var "ml_pass") `Eq` BExp TRUE) (Color (var "ml_tl") `Eq` Color Green) (Color (var "il_tl") `Eq` Color Green)

test5 = M.response (Color (var "ml_tl") `Eq` Color Green) (Color (var "il_tl") `Eq` Color Green)
test6 = M.response (Color (var "ml_tl") `Eq` Color Green) (var "a" `Gt` AInt 0)
test7 = M.response (AExp (var "d") `Eq` AExp (var "a" `Add` var "b")) (AExp (var "d") `Eq` AExp (var "b" `Add` var "c"))

test8 = M.globallyPrecedence (var "a" `Gt` AInt 0) (Color (var "ml_tl") `Eq` Color Green)
test9 = M.globallyPrecedence (var "c" `Gt` AInt 0) (Color (var "il_tl") `Eq` Color Green)
test10 = M.afterPrecedence (var "c" `Gt` AInt 0) (Color (var "ml_tl") `Eq` Color Green) (Color (var "il_tl") `Eq` Color Green)


testMakeGraph :: EventbMac -> IO ()
testMakeGraph mac = do
  g <- G.makeEventGraph mac
  initv <- G.initVertex (initenv mac) (G.vertices g)
  D.writeGraph (macname mac) g initv
