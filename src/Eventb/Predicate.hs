{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Eventb.Predicate where

import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Generics        as G
import           Data.List
import qualified Data.Map.Strict      as M
import           Data.SBV
import           Eventb
import qualified MySet                as S
import Debug.Trace

--define interpretation of new set for Z3
boolToBExp :: Bool -> BExp
boolToBExp True  = TRUE
boolToBExp False = FALSE
data Color = Red | Green deriving (Eq, Ord, Show, Read, G.Data, SymWord, HasKind, SatModel)
type SColor = SBV Eventb.Predicate.Color
sColor :: String -> Symbolic SColor
sColor = symbolic
sColors :: [String] -> Symbolic [SColor]
sColors = symbolics
colorToColor :: Eventb.Predicate.Color -> Eventb.Color
colorToColor Eventb.Predicate.Red   = Eventb.Red
colorToColor Eventb.Predicate.Green = Eventb.Green
type SData = SInteger
type SFile = SArray Integer Integer
data SMap = SMap {aExp :: M.Map String SInteger, bExp :: M.Map String SBool, color :: M.Map String SColor, filedata :: M.Map String SData, file :: M.Map String SFile}
sFiles :: [String] -> Symbolic [SFile]
sFiles = mapM newArray

extractAExpVar :: AExp -> Vars
extractAExpVar (AInt i)    = mempty
extractAExpVar (AVar v)    = mempty {aExp = S.singleton (show v)}
extractAExpVar (Add a1 a2) = extractAExpVar a1 `mappend` extractAExpVar a2
extractAExpVar (Sub a1 a2) = extractAExpVar a1 `mappend` extractAExpVar a2
extractAExpVar (Mul a1 a2) = extractAExpVar a1 `mappend` extractAExpVar a2
extractAExpVar (Div a1 a2) = extractAExpVar a1 `mappend` extractAExpVar a2

extractBExpVar :: BExp -> Vars
extractBExpVar (BVar v) = mempty {bExp = S.singleton (show v)}
extractBExpVar _        = mempty

extractColorVar :: Eventb.Color -> Vars
extractColorVar (CVar v) = mempty {color = S.singleton (show v)}
extractColorVar _        = mempty

extractDataVar :: Data -> Vars
extractDataVar (D a)      = extractAExpVar a
extractDataVar (Read f a) = extractFileVar f `mappend` extractAExpVar a
extractDataVar (DVar v)   = mempty {filedata = S.singleton (show v)}

extractFileVar :: File -> Vars
extractFileVar (FVar v) = mempty {file = S.singleton (show v)}
extractFileVar (Write f a d) = extractFileVar f `mappend` extractAExpVar a `mappend` extractDataVar d

extractValueVar :: Value -> Vars
extractValueVar (AExp a)  = extractAExpVar a
extractValueVar (BExp b)  = extractBExpVar b
extractValueVar (Color c) = extractColorVar c
extractValueVar (Data d)  = extractDataVar d
extractValueVar (File f)  = extractFileVar f

extractAPVar :: AP -> Vars
extractAPVar (Eq v1 v2) = extractValueVar v1 `mappend` extractValueVar v2
extractAPVar (Gt a1 a2) = extractAExpVar a1 `mappend` extractAExpVar a2

extractVariables :: Pred -> Vars
extractVariables T = mempty
extractVariables F = mempty
extractVariables (AP p) = extractAPVar p
extractVariables (And b1 b2) = extractVariables b1 `mappend` extractVariables b2
extractVariables (Or b1 b2) = extractVariables b1 `mappend` extractVariables b2
extractVariables (Not b) = extractVariables b
extractVariables (Imply b1 b2) = extractVariables b1 `mappend` extractVariables b2
extractVariables (Any (AExp (AVar (Const s))) p) = v{aExp = S.delete s $ aExp (v::Vars)}
  where
    v = extractVariables p
extractVariables (Any (BExp (BVar (Const s))) p) = v{bExp = S.delete s $ bExp (v::Vars)}
  where
    v = extractVariables p
extractVariables (Any (Color (CVar (Const s))) p) = v{color = S.delete s $ color (v::Vars)}
  where
    v = extractVariables p
extractVariables (Any (Data (DVar (Const s))) p) = v{color = S.delete s $ filedata (v::Vars)}
  where
    v = extractVariables p
extractVariables (Any (File (FVar (Const s))) p) = v{color = S.delete s $ file (v::Vars)}
  where
    v = extractVariables p

aExpToSInt :: AExp -> ReaderT SMap Symbolic SInteger
aExpToSInt (AInt i)    = return $ literal i
aExpToSInt (AVar v)    = do
  env <- ask
  return $ aExp (env :: SMap) M.! show v
aExpToSInt (Add a1 a2) = (+) <$> aExpToSInt a1 <*> aExpToSInt a2
aExpToSInt (Sub a1 a2) = (-) <$> aExpToSInt a1 <*> aExpToSInt a2
aExpToSInt (Mul a1 a2) = (*) <$> aExpToSInt a1 <*> aExpToSInt a2
aExpToSInt (Div a1 a2) = sDiv <$> aExpToSInt a1 <*> aExpToSInt a2

bExpToSBool :: BExp -> ReaderT SMap Symbolic SBool
bExpToSBool TRUE = return true
bExpToSBool FALSE = return false
bExpToSBool (BVar v) = do
  env <- ask
  return $ bExp (env :: SMap) M.! show v

colorToSColor :: Eventb.Color -> ReaderT SMap Symbolic SColor
colorToSColor Eventb.Red = return $ literal Eventb.Predicate.Red
colorToSColor Eventb.Green = return $ literal Eventb.Predicate.Green
colorToSColor (CVar v) = do
  env <- ask
  return $ color (env :: SMap) M.! show v

dataToSData :: Data -> ReaderT SMap Symbolic SData
dataToSData (D a) = aExpToSInt a
dataToSData (Read f a) = readArray <$> fileToSFile f <*> aExpToSInt a
dataToSData (DVar v) = do
  env <- ask
  return $ filedata (env :: SMap) M.! show v

fileToSFile :: File -> ReaderT SMap Symbolic SFile
fileToSFile (FVar v) = do
  env <- ask
  return $ file (env :: SMap) M.! show v
fileToSFile (Write f a d) = writeArray <$> fileToSFile f <*> aExpToSInt a <*> dataToSData d

apToPredicate :: AP -> ReaderT SMap Symbolic SBool
apToPredicate (Eq (AExp a1) (AExp a2)) = (.==) <$> aExpToSInt a1 <*> aExpToSInt a2
apToPredicate (Eq (BExp b1) (BExp b2)) = (.==) <$> bExpToSBool b1 <*> bExpToSBool b2
apToPredicate (Eq (Color c1) (Color c2)) = (.==) <$> colorToSColor c1 <*> colorToSColor c2
apToPredicate (Eq (Data d1) (Data d2)) = (.==) <$> dataToSData d1 <*> dataToSData d2
apToPredicate (Eq (File f1) (File f2)) = (.==) <$> fileToSFile f1 <*> fileToSFile f2
apToPredicate (Gt a1 a2) = (.>) <$> aExpToSInt a1 <*> aExpToSInt a2

predToPredicate :: Pred -> ReaderT SMap Symbolic SBool
predToPredicate T = return true
predToPredicate F = return false
predToPredicate (AP p) = apToPredicate p
predToPredicate (And b1 b2) = (&&&) <$> predToPredicate b1 <*> predToPredicate b2
predToPredicate (Or b1 b2) = (|||) <$> predToPredicate b1 <*> predToPredicate b2
predToPredicate (Not b) = bnot <$> predToPredicate b
predToPredicate (Imply b1 b2) = (==>) <$> predToPredicate b1 <*> predToPredicate b2
predToPredicate (Any (AExp (AVar (Const s))) p) = do
  env <- ask
  lift . forAll [s] $ \x -> runReaderT (predToPredicate p) ((env::SMap){aExp = M.insert s x $ aExp (env::SMap)})
predToPredicate (Any (BExp (BVar (Const s))) p) = do
  env <- ask
  lift . forAll [s] $ \x -> runReaderT (predToPredicate p) ((env::SMap){bExp = M.insert s x $ bExp (env::SMap)})
predToPredicate (Any (Color (CVar (Const s))) p) = do
  env <- ask
  lift . forAll [s] $ \x -> runReaderT (predToPredicate p) ((env::SMap){color = M.insert s x $ color (env::SMap)})
predToPredicate (Any (Data (DVar (Const s))) p) = do
  env <- ask
  lift . forAll [s] $ \x -> runReaderT (predToPredicate p) ((env::SMap){color = M.insert s x $ color (env::SMap)})
predToPredicate (Any (File (FVar (Const s))) p) = do
  env <- ask
  lift . forAll [s] $ \x -> runReaderT (predToPredicate p) ((env::SMap){color = M.insert s x $ color (env::SMap)})

-- alphaConversion :: Pred -> Reader Var Pred
-- alphaConversion (And b1 b2) = And <$> alphaConversion b1 <*> alphaConversion b2
-- alphaConversion (Or b1 b2) = Or <$> alphaConversion b1 <*> alphaConversion b2
-- alphaConversion (Not b) = Not <$> alphaConversion b
-- alphaConversion (Imply b1 b2) = Imply <$> alphaConversion b1 <*> alphaConversion b2
-- alphaConversion (Any (AExp (AVar (Const s))) p)


varsToSMap :: Vars -> Symbolic SMap
varsToSMap vars = do
  let aExpVars = S.toList $ aExp (vars :: Vars)
      bExpVars = S.toList $ bExp (vars :: Vars)
      colorVars = S.toList $ color (vars :: Vars)
      dataVars = S.toList $ filedata (vars :: Vars)
      fileVars = S.toList $ file (vars :: Vars)
  sints <- sIntegers aExpVars
  sbools <- sBools bExpVars
  scolors <- sColors colorVars
  sdatas <- sIntegers dataVars
  sfiles <- sFiles fileVars
  return SMap { aExp = M.fromList $ zip aExpVars sints
              , bExp = M.fromList $ zip bExpVars sbools
              , color = M.fromList $ zip colorVars scolors
              , filedata = M.fromList $ zip dataVars sdatas
              , file = M.fromList $ zip fileVars sfiles
              }

isUnsatisfiable :: Pred -> IO Bool
isUnsatisfiable b = fmap (not . modelExists) . sat $ varsToSMap (extractVariables b) >>= runReaderT (predToPredicate b)

isEquivalent :: Pred -> Pred -> IO Bool
isEquivalent b1 b2 = fmap (not . modelExists) . sat $ varsToSMap (extractVariables b1 `mappend` extractVariables b2) >>= runReaderT ((. bnot) . (<=>) <$> predToPredicate b1 <*> predToPredicate b2)

minimizePred :: Pred -> IO Pred
minimizePred b = do
  b' <- (`runReaderT` b) . (`evalStateT` id) $ minimizePred' b
  if b == b'
    then return b'
    else minimizePred b'

minimizePred' :: Pred -> StateT (Pred -> Pred) (ReaderT Pred IO) Pred
minimizePred' (And b1 b2) = do
  res <- choice [(b1, minimizePred' b1), (b2, minimizePred' b2), (F, return F)]
  case res of
    Just x -> return x
    Nothing -> do
      f <- get
      b1' <- put (f . And b2) >> minimizePred' b1
      b2' <- put (f . And b1') >> minimizePred' b2
      return $ And b1' b2'
minimizePred' (Or b1 b2) = do
  res <- choice [(b1, minimizePred' b1), (b2, minimizePred' b2), (T, return T)]
  case res of
    Just x -> return x
    Nothing -> do
      f <- get
      b1' <- put (f . Or b2) >> minimizePred' b1
      b2' <- put (f . Or b1') >> minimizePred' b2
      return $ Or b1' b2'
minimizePred' (Not (Not b)) = minimizePred' b
minimizePred' (Not b) = Not <$> withStateT (. Not) (minimizePred' b)
minimizePred' (Imply b1 b2) = do
  res <- choice [(Not b1, minimizePred' $ Not b1), (b2, minimizePred' b2), (T, return T)]
  case res of
    Just x -> return x
    Nothing -> do
      f <- get
      b1' <- put (f . (`Imply` b2)) >> minimizePred' b1
      b2' <- put (f . Imply b1') >> minimizePred' b2
      return $ Imply b1' b2'
minimizePred' b = traceShow (b) (return ()) >> return b

choice :: [(Pred, StateT (Pred -> Pred) (ReaderT Pred IO) Pred)] -> StateT (Pred -> Pred) (ReaderT Pred IO) (Maybe Pred)
choice = foldl' (\x y -> mplus <$> x <*> p y) (return Nothing)
  where
    p (obj, result) = do
      f <- get
      b <- lift $ isEquivalentToBody (f obj)
      if b
        then Just <$> result
        else return Nothing :: StateT (Pred -> Pred) (ReaderT Pred IO) (Maybe Pred)

isEquivalentToBody :: Pred -> ReaderT Pred IO Bool
isEquivalentToBody p = do
  body <- ask
  lift . fmap (not . modelExists) . sat $ varsToSMap (extractVariables body) >>= fmap bnot . runReaderT ((<=>) <$> predToPredicate body <*> predToPredicate p)

afterVar :: Var -> Var
afterVar (Var v)   = NewVar v
afterVar (Const v) = Const v

afterAExp :: AExp -> AExp
afterAExp (AVar v)    = AVar $ afterVar v
afterAExp (Add a1 a2) = afterAExp a1 `Add` afterAExp a2
afterAExp (Sub a1 a2) = afterAExp a1 `Sub` afterAExp a2
afterAExp (Mul a1 a2) = afterAExp a1 `Mul` afterAExp a2
afterAExp (Div a1 a2) = afterAExp a1 `Div` afterAExp a2
afterAExp a           = a

afterBExp :: BExp -> BExp
afterBExp (BVar v) = BVar $ afterVar v
afterBExp b        = b

afterColor :: Eventb.Color -> Eventb.Color
afterColor (CVar v) = CVar $ afterVar v
afterColor c        = c

afterData :: Data -> Data
afterData (D a)      = D $ afterAExp a
afterData (Read f a) = Read (afterFile f) (afterAExp a)
afterData (DVar v)   = DVar $ afterVar v

afterFile :: File -> File
afterFile (FVar v)      = FVar $ afterVar v
afterFile (Write f a d) = Write (afterFile f) (afterAExp a) (afterData d)

afterValue :: Value -> Value
afterValue (AExp a)  = AExp $ afterAExp a
afterValue (BExp b)  = BExp $ afterBExp b
afterValue (Color c) = Color $ afterColor c
afterValue (Data d)  = Data $ afterData d
afterValue (File f)  = File $ afterFile f

afterAP :: AP -> AP
afterAP  (Eq v1 v2) = afterValue v1 `Eq` afterValue v2
afterAP (Gt a1 a2)  = afterAExp a1 `Gt` afterAExp a2

afterPred :: Pred -> Pred
afterPred T             = T
afterPred F             = F
afterPred (AP p)        = AP $ afterAP p
afterPred (And p1 p2)   = afterPred p1 `And` afterPred p2
afterPred (Or p1 p2)    = afterPred p1 `Or` afterPred p2
afterPred (Not p)       = Not $ afterPred p
afterPred (Imply p1 p2) = afterPred p1 `Imply` afterPred p2
afterPred (Any v p)     = Any v $ afterPred p

updateAExp :: AExp -> Reader Env AExp
updateAExp a@(AVar (Var v)) = do
  env <- ask
  case M.lookup v env of
    Just (AExp value) -> return value
    Nothing           -> return a
updateAExp a@(AVar (Const v)) = return a
updateAExp a@(AInt i') = return a
updateAExp (Add a1 a2) = Add <$> updateAExp a1 <*> updateAExp a2
updateAExp (Sub a1 a2) = Sub <$> updateAExp a1 <*> updateAExp a2
updateAExp (Mul a1 a2) = Mul <$> updateAExp a1 <*> updateAExp a2
updateAExp (Div a1 a2) = Div <$> updateAExp a1 <*> updateAExp a2

updateBExp :: BExp -> Reader Env BExp
updateBExp b@(BVar (Var v)) = do
  env <- ask
  case M.lookup v env of
    Just (BExp value) -> return value
    Nothing           -> return b
updateBExp b = return b

updateColor :: Eventb.Color -> Reader Env Eventb.Color
updateColor c@(CVar (Var v)) = do
  env <- ask
  case  M.lookup v env of
    Just (Color value) -> return value
    Nothing            -> return c
updateColor c = return c

updateData :: Data -> Reader Env Data
updateData d@(DVar (Var v)) = do
  env <- ask
  case M.lookup v env of
    Just (Data value) -> return value
    Nothing           -> return d
updateData (D a) = D <$> updateAExp a
updateData (Read f a) = Read <$> updateFile f <*> updateAExp a

updateFile :: File -> Reader Env File
updateFile f@(FVar (Var v)) = do
  env <- ask
  case M.lookup v env of
    Just (File value) -> return value
    Nothing           -> return f
updateFile f@(FVar (Const v)) = return f
updateFile (Write f a d) = Write <$> updateFile f <*>updateAExp a <*> updateData d

updateValue :: Value -> Reader Env Value
updateValue (AExp a)  = AExp <$> updateAExp a
updateValue (BExp b)  = BExp <$> updateBExp b
updateValue (Color c) = Color <$> updateColor c
updateValue (Data d)  = Data <$> updateData d
updateValue (File f)  = File <$> updateFile f

updateAP :: AP -> Reader Env AP
updateAP (Eq v1 v2) = Eq <$> updateValue v1 <*> updateValue v2
updateAP (Gt a1 a2) = Gt <$> updateAExp a1 <*> updateAExp a2

updatePred :: Pred -> Reader Env Pred
updatePred T             = return T
updatePred F             = return F
updatePred (AP p)        = AP <$> updateAP p
updatePred (And b1 b2)   = And <$> updatePred b1 <*> updatePred b2
updatePred (Or b1 b2)    = Or <$> updatePred b1 <*> updatePred b2
updatePred (Not b)       = Not <$> updatePred b
updatePred (Imply b1 b2) = Imply <$> updatePred b1 <*>updatePred b2
