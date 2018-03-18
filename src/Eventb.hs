{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Eventb where

import           Control.DeepSeq
import           Data.List
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Data.Ord()
import           GHC.Generics
import qualified MySet           as S

-- followings are about data structure
class HasVar a where
  var    :: String -> a
  newvar :: String -> a
  constant :: String -> a


data Var = Var String | NewVar String | Const String deriving (Eq, Ord, Generic, NFData)
data AExp = AInt Integer | AVar Var | Add AExp AExp | Sub AExp AExp | Mul AExp AExp | Div AExp AExp deriving (Eq, Ord, Generic, NFData)
data BExp = TRUE | FALSE | BVar Var deriving (Eq, Ord, Generic, NFData)
data Color = Red | Green | CVar Var deriving (Eq, Ord, Generic, NFData)
data Data = D AExp | Read File AExp | DVar Var deriving (Eq, Ord, Generic, NFData)
data File = FVar Var | Write File AExp Data deriving (Eq, Ord, Generic, NFData)
data Value = AExp AExp | BExp BExp | Color Color | Data Data | File File deriving (Eq, Ord, Generic, NFData)
data AP =  Eq Value Value | Gt AExp AExp deriving (Eq, Ord, Generic, NFData)
data Pred = T | F | AP AP| And Pred Pred | Or Pred Pred | Not Pred | Imply Pred Pred | Any Value Pred deriving (Eq, Ord, Generic, NFData)


instance HasVar AExp where
  var = AVar . Var
  newvar = AVar . NewVar
  constant = AVar . Const
instance HasVar BExp where
  var = BVar . Var
  newvar = BVar . NewVar
  constant = BVar . Const
instance HasVar Color where
  var = CVar . Var
  newvar = CVar . NewVar
  constant = CVar . Const
instance HasVar Data where
  var = DVar . Var
  newvar = DVar . NewVar
  constant = DVar . Const
instance HasVar File where
  var = FVar . Var
  newvar = FVar . NewVar
  constant = FVar . Const
instance Show Var where
  show (Var v)    = v
  show (NewVar v) = v `mappend` "'"
  show (Const v)  = v
instance Show AExp where
  show (AInt i)    = show i
  show (AVar v)    = show v
  show (Add a1 a2) = concat [show a1,"+",show a2]
  show (Sub a1 a2) = concat [show a1,"-",show a2]
  show (Mul a1 a2) = concat ["(",show a1,")*(",show a2,")"]
  show (Div a1 a2) = concat ["(",show a1,")/(",show a2,")"]
instance Show BExp where
  show TRUE     = "TRUE"
  show FALSE    = "FALSE"
  show (BVar v) = show v
instance Show Color where
  show (CVar v) = show v
  show Red      = "red"
  show Green    = "green"
instance Show Data where
  show (D i)      = "Data " `mappend` show i
  show (Read f a) = mconcat [show f, "(", show a, ")"]
  show (DVar v)   = show v
instance Show File where
  show (FVar v)      = show v
  show (Write f a d) = mconcat ["Set ", show f, "(", show a, ")=", show d]
instance Show Value where
  show (AExp a)  = show a
  show (BExp b)  = show b
  show (Color c) = show c
  show (Data d)  = show d
  show (File f)  = show f
instance Show AP where
  show (Eq v1 v2) = concat ["{",show v1,"=",show v2,"}"]
  show (Gt a1 a2) = concat ["{",show a1,">",show a2,"}"]
instance Show Pred where
  show T             = "true"
  show F             = "false"
  show (AP p)        = show p
  show (And b1 b2)   = concat [show b1,"&",show b2]
  show (Or b1 b2)    = concat ["((",show b1,")or(",show b2,"))"]
  show (Not b)       = concat ["not(",show b,")"]
  show (Imply b1 b2) = concat ["(",show b1,"=>",show b2,")"]
  show (Any v p)     = concat ["forany ", show v , ".", show p]
instance Monoid Pred where
  mempty = T
  mappend = And


type Env = M.Map String Value
type Axiom = Pred
type BAPred = Pred
type Inv = Pred
type Grd = Pred
type EventName = String
data Termination = Ordinary | Convergent deriving (Eq, Show, Ord)
data Vars = Vars {aExp :: S.Set String, bExp :: S.Set String, color :: S.Set String, filedata :: S.Set String, file :: S.Set String } deriving (Show)
data Event = Event {name :: EventName, refine :: [Event], grds :: [Pred], acts :: [BAPred], termination :: Termination} deriving (Eq, Ord)
data EventbCtx = EventbCtx {extends :: [EventbCtx], consts :: [String], axioms :: [Axiom]} deriving (Show)
data EventbMac = EventbMac {macname :: String, refines :: [EventbMac], sees :: [EventbCtx], vars :: Vars, invs :: [Inv], initenv :: Env, events :: [Event]} deriving (Show)

instance Show Event where
  show = name
instance Monoid Vars where
  mempty = Vars S.empty S.empty S.empty S.empty S.empty
  mappend v1 v2
    = Vars {aExp = aExp v1 `S.union` aExp v2, bExp = bExp v1 `S.union` bExp v2, color = color v1 `S.union` color v2, filedata = filedata v1 `S.union` filedata v2, file = file v1 `S.union` file v2}

diff :: Vars -> Vars -> Vars
diff v1 v2 = Vars {aExp = aExp v1 S.\\ aExp v2, bExp = bExp v1 S.\\ bExp v2, color = color v1 S.\\ color v2, filedata = filedata v1 S.\\ filedata v2, file = file v1 S.\\ file v2}

forany :: Vars -> Pred -> Pred
forany v p
  | not . S.null $ aExp v = Any (AExp (constant . S.findMin $ aExp v)) $ forany (v{aExp = S.deleteMin $ aExp v}) p
  | not . S.null $ bExp v = Any (BExp (constant . S.findMin $ bExp v)) $ forany (v{bExp = S.deleteMin $ bExp v}) p
  | not . S.null $ color v = Any (Color (constant . S.findMin $ color v)) $ forany (v{color = S.deleteMin $ color v}) p
  | not . S.null $ filedata v = Any (Color (constant . S.findMin $ filedata v)) $ forany (v{filedata = S.deleteMin $ filedata v}) p
  | not . S.null $ file v = Any (Color (constant . S.findMin $ file v)) $ forany (v{file = S.deleteMin $ file v}) p
  | otherwise = p

grd :: Event -> Pred
grd = mconcat . grds

act :: Event -> Pred
act = mconcat . acts

invAll :: EventbMac -> Pred
invAll mac = mconcat (invs mac) `mappend` (mconcat . fmap axiomAll $ sees mac) `mappend` (mconcat . fmap invAll $ refines mac)

axiomAll :: EventbCtx -> Pred
axiomAll ctx = mconcat (axioms ctx) `mappend` (mconcat . fmap axiomAll $ extends ctx)

eventOf :: EventName -> EventbMac -> Event
eventOf str = fromJust . find ((==) str . name) . events

completeEvent :: EventbMac -> EventbMac
completeEvent mac = mac {events = fmap complete (events mac)}
  where
    identityAExp s = AExp (newvar s) `Eq` AExp (var s)
    identityBExp s = BExp (newvar s) `Eq` BExp (var s)
    identityColor s = Color (newvar s) `Eq` Color (var s)
    identityD s = Data (newvar s) `Eq` Data (var s)
    identityFile s = File (newvar s) `Eq` File (var s)
    identityPred v = mconcat . zipWith ($) (((`S.foldr` []) . (((:) . AP) .)) <$> [identityAExp, identityBExp, identityColor, identityD, identityFile]) $ [aExp, bExp, color, filedata, file] <*> [v]
    collectAllVars m = vars m `mappend` foldr (mappend . collectAllVars) mempty (refines m)
    collectAllEvents evt = acts evt `mappend` foldr (mappend . collectAllEvents) mempty (refine evt)
    complete evt = evt {acts = mappend (collectAllEvents evt) . identityPred $ collectAllVars mac `diff` foldr (mappend . extractNewVariables) mempty (collectAllEvents evt)}

extractNewVariables :: Pred -> Vars
extractNewVariables T = mempty
extractNewVariables F = mempty
extractNewVariables (AP p) = extractNewAPVar p
extractNewVariables (And b1 b2) = extractNewVariables b1 `mappend` extractNewVariables b2
extractNewVariables (Or b1 b2) = extractNewVariables b1 `mappend` extractNewVariables b2
extractNewVariables (Not b) = extractNewVariables b
extractNewVariables (Imply b1 b2) = extractNewVariables b1 `mappend` extractNewVariables b2

extractNewAPVar :: AP -> Vars
extractNewAPVar (Eq v1 v2) = extractNewValueVar v1 `mappend` extractNewValueVar v2
extractNewAPVar (Gt a1 a2) = extractNewAExpVar a1 `mappend` extractNewAExpVar a2

extractNewValueVar :: Value -> Vars
extractNewValueVar (AExp a)  = extractNewAExpVar a
extractNewValueVar (BExp b)  = extractNewBExpVar b
extractNewValueVar (Color c) = extractNewColorVar c
extractNewValueVar (Data d)  = extractNewDVar d
extractNewValueVar (File f)  = extractNewFileVar f

extractNewAExpVar :: AExp -> Vars
extractNewAExpVar (AInt _)    = mempty
extractNewAExpVar (AVar v)    = mempty {aExp = extractNewVar v}
extractNewAExpVar (Add a1 a2) = extractNewAExpVar a1 `mappend` extractNewAExpVar a2
extractNewAExpVar (Sub a1 a2) = extractNewAExpVar a1 `mappend` extractNewAExpVar a2
extractNewAExpVar (Mul a1 a2) = extractNewAExpVar a1 `mappend` extractNewAExpVar a2
extractNewAExpVar (Div a1 a2) = extractNewAExpVar a1 `mappend` extractNewAExpVar a2

extractNewBExpVar :: BExp -> Vars
extractNewBExpVar (BVar v) = mempty {bExp = extractNewVar v}
extractNewBExpVar _        = mempty

extractNewColorVar :: Color -> Vars
extractNewColorVar (CVar v) = mempty {color = extractNewVar v}
extractNewColorVar _        = mempty

extractNewDVar :: Data -> Vars
extractNewDVar (DVar v)   = mempty {filedata = extractNewVar v}
extractNewDVar (Read f a) = extractNewFileVar f `mappend` extractNewAExpVar a

extractNewFileVar :: File -> Vars
extractNewFileVar (FVar v) = mempty {file = extractNewVar v}
extractNewFileVar (Write f a d) = extractNewFileVar f `mappend` extractNewAExpVar a `mappend` extractNewDVar d

extractNewVar :: Var -> S.Set String
extractNewVar (Var _)    = mempty
extractNewVar (NewVar v) = S.singleton v
extractNewVar (Const _)  = mempty

------------------------ followings are test case ------------------------------------------------------------------------
-- controlling traffic lights
ctx0 :: EventbCtx
ctx0 = EventbCtx {extends = [], consts = ["d"], axioms = [AP $ constant "d" `Gt` AInt 0]}

mac0 :: EventbMac
mac0 = EventbMac { macname = "mac0"
                 , refines = []
                 , sees = [ctx0]
                 , vars = mempty {aExp = S.fromList ["n"]}
                 , invs = [ AP (constant "d" `Gt` var "n") `Or` AP (AExp (constant "d") `Eq` AExp (var "n"))
                         , AP (var "n" `Gt` AInt 0) `Or` AP (AExp (var "n") `Eq` AExp (AInt 0))
                         ]
                 , initenv = M.singleton "n" (AExp (AInt 0))
                 , events = [ Event { name = "ML_out"
                                    , refine = []
                                    , grds = [ AP $ constant "d" `Gt` var "n"
                                            ]
                                    , acts = [ AP $ AExp (newvar "n") `Eq` AExp (var "n" `Add` AInt 1)
                                            ]
                                    , termination = Ordinary
                                    }
                            , Event { name = "ML_in"
                                    , refine = []
                                    , grds = [ AP $ var "n" `Gt` AInt 0
                                            ]
                                    , acts = [ AP $ AExp (newvar "n") `Eq` AExp (var "n" `Sub` AInt 1)
                                            ]
                                    , termination = Ordinary
                                    }
                            ]
                 }

mac1 :: EventbMac
mac1 = EventbMac { macname = "mac1"
                 , refines = [mac0]
                 , sees = [ctx0]
                 , vars = mempty {aExp = S.fromList ["a", "b", "c"]}
                 , invs = [ AP (AExp (var "a") `Eq` AExp (AInt 0)) `Or` AP (var "a" `Gt` AInt 0)
                         , AP (AExp (var "b") `Eq` AExp (AInt 0)) `Or` AP (var "b" `Gt` AInt 0)
                         , AP (AExp (var "c") `Eq` AExp (AInt 0)) `Or` AP (var "c" `Gt` AInt 0)
                         , AP $ AExp (var "a" `Add` var "b" `Add` var "c") `Eq` AExp (var "n")
                         , AP (AExp (var "a") `Eq` AExp (AInt 0)) `Or` AP (AExp (var "c") `Eq` AExp (AInt 0))
                         ]
                 , initenv = M.fromList [ ("a", AExp $ AInt 0)
                                        , ("b", AExp $ AInt 0)
                                        , ("c", AExp $ AInt 0)
                                        ]
                 , events = [ Event { name = "ML_out"
                                    , refine = ["ML_out" `eventOf` mac0]
                                    , grds = [ AP $ constant "d" `Gt` (var "a" `Add` var "b")
                                            , AP $ AExp (var "c") `Eq` AExp (AInt 0)
                                            ]
                                    , acts = [ AP $ AExp (newvar "a") `Eq` AExp (var "a" `Add` AInt 1)
                                            ]
                                    , termination = Ordinary
                                    }
                            , Event { name = "ML_in"
                                    , refine = ["ML_in" `eventOf` mac0]
                                    , grds = [ AP $ var "c" `Gt` AInt 0 ]
                                    , acts = [ AP $ AExp (newvar "c") `Eq` AExp (var "c" `Sub` AInt 1)
                                            ]
                                    , termination = Ordinary
                                    }
                            , Event { name = "IL_in"
                                    , refine = []
                                    , grds = [ AP $ AVar (Var "a") `Gt` AInt 0 ]
                                    , acts = [ AP $ AExp (newvar "a") `Eq` AExp (var "a" `Sub` AInt 1)
                                            , AP $ AExp (newvar "b") `Eq` AExp (var "b" `Add` AInt 1)
                                            ]
                                    , termination = Convergent
                                    }
                            , Event { name = "IL_out"
                                    , refine = []
                                    , grds = [ AP $ var "b" `Gt` AInt 0
                                            , AP $ AExp (var "a") `Eq` AExp (AInt 0)
                                            ]
                                    , acts = [ AP $ AExp (newvar "b") `Eq` AExp (var "b" `Sub` AInt 1)
                                            , AP $ AExp (newvar "c") `Eq` AExp (var "c" `Add` AInt 1)
                                            ]
                                    , termination = Convergent
                                    }
                            ]
                 }

ctx1 :: EventbCtx
ctx1 = EventbCtx { extends = [ctx0]
                 , consts = ["red", "green"]
                 , axioms = []
                 }

mac2 :: EventbMac
mac2 = EventbMac { macname = "mac2"
                 , refines = [mac1]
                 , sees = [ctx1]
                 , vars = mempty {aExp = S.fromList ["a","b","c"], bExp = S.fromList ["ml_pass","il_pass"], color = S.fromList ["ml_tl","il_tl"]}
                 , invs = [ AP (Color (var "ml_tl") `Eq` Color Green) `Imply` (AP (constant "d" `Gt` (var "a" `Add` var "b")) `And` AP (AExp (var "c") `Eq` AExp (AInt 0)))
                         , AP (Color (var "il_tl") `Eq` Color Green) `Imply` (AP (var "b" `Gt` AInt 0) `And` AP (AExp (var "a") `Eq` AExp (AInt 0)))
                         , AP (Color (var "ml_tl") `Eq` Color Red) `Or` AP (Color (var "il_tl") `Eq` Color Red)
                         , AP (Color (var "ml_tl") `Eq` Color Red) `Imply` AP (BExp (var "ml_pass") `Eq` BExp TRUE)
                         , AP (Color (var "il_tl") `Eq` Color Red) `Imply` AP (BExp (var "il_pass") `Eq` BExp TRUE)
                         ]
                  , initenv = M.fromList [ ("a", AExp $ AInt 0)
                                         , ("b", AExp $ AInt 0)
                                         , ("c", AExp $ AInt 0)
                                         , ("ml_tl", Color Red)
                                         , ("il_tl", Color Red)
                                         , ("ml_pass", BExp TRUE)
                                         , ("il_pass", BExp TRUE)
                                         ]
                  , events = [ Event { name = "ML_out_1"
                                     , refine = ["ML_out" `eventOf` mac1]
                                     , grds = [ AP $ Color (var "ml_tl") `Eq` Color Green
                                             , Not . AP $ (AExp (var "a" `Add` var "b" `Add` AInt 1) `Eq` AExp (constant "d"))
                                             ]
                                     , acts = [ AP $ AExp (newvar "a") `Eq` AExp (var  "a" `Add` AInt 1)
                                             , AP $ BExp (newvar "ml_pass") `Eq` BExp TRUE
                                             ]
                                     , termination = Ordinary
                                     }
                             , Event { name = "ML_out_2"
                                     , refine = ["ML_out" `eventOf` mac1]
                                     , grds = [ AP $ Color (var "ml_tl") `Eq` Color Green
                                             , AP $ AExp (var "a" `Add` var "b" `Add` AInt 1) `Eq` AExp (constant "d")
                                             ]
                                     , acts = [ AP $ AExp (newvar "a") `Eq` AExp (var "a" `Add` AInt 1)
                                             , AP $ Color (newvar "ml_tl") `Eq` Color Red
                                             , AP $ BExp (newvar "ml_pass") `Eq` BExp TRUE
                                             ]
                                     , termination = Ordinary
                                      }
                             , Event { name = "ML_in"
                                     , refine = ["ML_in" `eventOf` mac1]
                                     , grds = [ AP $ var "c" `Gt` AInt 0 ]
                                     , acts = [ AP $ AExp (newvar "c") `Eq` AExp (var "c" `Sub` AInt 1)
                                             ]
                                     , termination = Ordinary
                                     }
                             , Event { name = "IL_in"
                                     , refine = ["IL_in" `eventOf` mac1]
                                     , grds = [ AP $ var "a" `Gt` AInt 0 ]
                                     , acts = [ AP $ AExp (newvar "a") `Eq` AExp (var "a" `Sub` AInt 1)
                                             , AP $ AExp (newvar "b") `Eq` AExp (var "b" `Add` AInt 1)
                                             ]
                                     , termination = Ordinary
                                     }
                             , Event { name = "IL_out_1"
                                     , refine = ["IL_out" `eventOf` mac1]
                                     , grds = [ AP $ Color (var "il_tl") `Eq` Color Green
                                             , Not . AP $ (AExp (var "b") `Eq` AExp (AInt 1))
                                             ]
                                     , acts = [ AP $ AExp (newvar "b") `Eq` AExp (var "b" `Sub` AInt 1)
                                             , AP $ AExp (newvar "c") `Eq` AExp (var "c" `Add` AInt 1)
                                             , AP $ BExp (newvar "il_pass") `Eq` BExp TRUE
                                             ]
                                     , termination = Ordinary
                                     }
                             , Event { name = "IL_out_2"
                                     , refine = ["IL_out" `eventOf` mac1]
                                     , grds = [ AP $ Color (var "il_tl") `Eq` Color Green
                                             , AP $ AExp (var "b") `Eq` AExp (AInt 1)
                                             ]
                                     , acts = [ AP $ AExp (newvar "b") `Eq` AExp (var "b" `Sub` AInt 1)
                                             , AP $ AExp (newvar "c") `Eq` AExp (var "c" `Add` AInt 1)
                                             , AP $ Color (newvar "il_tl") `Eq` Color Red
                                             , AP $ BExp (newvar "il_pass") `Eq` BExp TRUE
                                             ]
                                     , termination = Ordinary
                                     }
                             , Event { name = "ML_tl_green"
                                     , refine = []
                                     , grds = [ AP $ Color (var "ml_tl") `Eq` Color Red
                                             , AP $ constant "d" `Gt` (var "a" `Add` var "b")
                                             , AP $ AExp (var "c") `Eq` AExp (AInt 0)
                                             , AP $ BExp (var "il_pass") `Eq` BExp TRUE
                                             ]
                                     , acts = [ AP $ Color (CVar (NewVar "ml_tl")) `Eq` Color Green
                                             , AP $ Color (CVar (NewVar "il_tl")) `Eq` Color Red
                                             , AP $ BExp (BVar (NewVar "ml_pass")) `Eq` BExp FALSE
                                             ]
                                     , termination = Convergent
                                     }
                             , Event { name = "IL_tl_green"
                                     , refine = []
                                     , grds = [ AP $ Color (CVar (Var "il_tl")) `Eq` Color Red
                                             , AP $ AVar (Var "b") `Gt` AInt 0
                                             , AP $ AExp (AVar (Var "a")) `Eq` AExp (AInt 0)
                                             , AP $ BExp (BVar (Var "ml_pass")) `Eq` BExp TRUE
                                             ]
                                     , acts = [ AP $ Color (CVar (NewVar "il_tl")) `Eq` Color Green
                                             , AP $ Color (CVar (NewVar "ml_tl")) `Eq` Color Red
                                             , AP $ BExp (BVar (NewVar "il_pass")) `Eq` BExp FALSE
                                             ]
                                     , termination = Convergent
                                     }
                             ]
                  }

mac2' :: EventbMac
mac2' = mac2 { macname = "mac2'"
             , invs = invs mac2 `mappend` [ AP (var "a" `Gt` AInt 0) `Imply` AP (BExp (var "ml_pass") `Eq` BExp TRUE)
                                        , AP (var "c" `Gt` AInt 0) `Imply` AP (BExp (var "il_pass") `Eq` BExp TRUE)
                                        , (AP (Color (var "ml_tl") `Eq` Color Red) `And` Not (AP (AExp (var "a" `Add` var "b") `Eq` AExp (constant "d")))) `Imply` AP (AExp (var "a") `Eq` AExp (AInt 0))
                                        , (AP (Color (var "il_tl") `Eq` Color Red) `And` Not (AP (AExp (var "b") `Eq` AExp (AInt 0)))) `Imply` AP (AExp (var "c") `Eq` AExp (AInt 0))
                                        , Not (AP (AExp (var "a") `Eq` AExp (AInt 0)) `And` AP (var "b" `Gt` AInt 0) `And` AP (constant "d" `Gt` var "b") `And` AP (AExp (var "c") `Eq` AExp (AInt 0)) `And` AP (Color (var "ml_tl") `Eq` Color Red) `And` AP (Color (var "il_tl") `Eq` Color Red) `And` AP (BExp (var "ml_pass") `Eq` BExp TRUE) `And` AP (BExp (var "il_pass") `Eq` BExp TRUE))
                                        , (AP (AExp (var "a") `Eq` AExp (AInt 0)) `And` AP (AExp (var "b") `Eq` AExp (AInt 0)) `And` AP (Color (var "ml_tl") `Eq` Color Green)) `Imply` AP (BExp (var "ml_pass") `Eq` BExp FALSE)
                                        , (AP (AExp (var "c") `Eq` AExp (AInt 0)) `And` AP (AExp (var "b") `Eq` AExp (constant "d")) `And` AP (Color (var "il_tl") `Eq` Color Green)) `Imply` AP (BExp (var "il_pass") `Eq` BExp FALSE)
                                        ]
             }

-- a simple file transfer protocol
ftp_ctx0 :: EventbCtx
ftp_ctx0 = EventbCtx {extends = [], consts = ["n","f"], axioms = [AP $ constant "n" `Gt` AInt 0]}

ftp_mac0 :: EventbMac
ftp_mac0 = EventbMac { macname = "ftp_mac0"
                     , refines = []
                     , sees = [ftp_ctx0]
                     , vars = mempty {bExp = S.fromList ["b"], filedata = S.fromList ["g"]}
                     , invs = [AP (BExp (var "b") `Eq` BExp TRUE) `Imply` AP (File (constant "f") `Eq` File (var "g"))]
                     , initenv = M.fromList [("b",BExp FALSE)]
                     , events = [ Event { name = "final"
                                        , refine = []
                                        , grds = [ AP $ BExp (var "b") `Eq` BExp FALSE
                                                ]
                                        , acts = [ AP $ File (newvar "g") `Eq` File (constant "f")
                                                , AP $ BExp (newvar "b") `Eq` BExp TRUE]
                                        , termination = Ordinary
                                        }
                                ]
                     }

ftp_mac1 :: EventbMac
ftp_mac1 = EventbMac { macname = "ftp_mac1"
                     , refines = [ftp_mac0]
                     , sees = [ftp_ctx0]
                     , vars = mempty {aExp = S.fromList ["r"], bExp = S.fromList ["b"], filedata = S.fromList ["h"]}
                     , invs = [ AP (var "r" `Gt` AInt 0) `And` (AP (constant "n" `Add` AInt 1 `Gt` var "r") `Or` AP (AExp (constant "n" `Add` AInt 1) `Eq` AExp (var "r")))
                             , Any (AExp (constant "i")) $ (AP (constant "i" `Gt` AInt 0) `And` AP (var "r" `Gt` constant "i")) `Imply` AP (Data (Read (constant "f") (constant "i")) `Eq` Data (Read (var "h") (constant "i")))
                             , AP (BExp (var "b") `Eq` BExp TRUE) `Imply` AP (AExp (var "r") `Eq` AExp (constant "n" `Add` AInt 1))
                             , AP (BExp (var "b") `Eq` BExp TRUE) `Imply` AP (File (var "g") `Eq` File (var "h"))
                             ]
                     , initenv = M.fromList [("b", BExp FALSE), ("r", AExp (AInt 1))]
                     , events = [ Event { name = "final"
                                        , refine = ["final" `eventOf` ftp_mac0]
                                        , grds = [ AP $ BExp (var "b") `Eq` BExp FALSE
                                                , AP $ AExp (var "r") `Eq` AExp (constant "n" `Add` AInt 1)
                                                ]
                                        , acts = [ AP $ BExp (newvar "b") `Eq` BExp TRUE
                                                ]
                                        , termination = Ordinary
                                        }
                                , Event { name = "receive"
                                        , refine = []
                                        , grds = [ AP (constant "n" `Gt` var "r") `Or` AP (AExp (constant "n") `Eq` AExp (var "r"))
                                                ]
                                        , acts = [ AP $ File (newvar "h") `Eq` File (Write (var "h") (var "r") (Read (constant "f" ) (var "r")))
                                                , AP $ AExp (newvar "r") `Eq` AExp (var "r" `Add` AInt 1)
                                                ]
                                        , termination = Convergent
                                        }
                                ]
                      }

hoge :: EventbMac
hoge = EventbMac { macname = ""
, refines = []
, sees = [ftp_ctx0]
, vars = mempty {aExp = S.fromList ["r"], bExp = S.fromList ["b"], filedata = S.fromList ["h"]}
, invs = [ Any (AExp (constant "i")) $ (AP (constant "i" `Gt` AInt 0) `And` AP (var "r" `Gt` constant "i")) `Imply` AP (Data (Read (constant "f") (constant "i")) `Eq` Data (Read (var "h") (constant "i")))
        ]
, initenv = M.fromList [("b", BExp FALSE), ("r", AExp (AInt 1))]
, events = [ ]

}