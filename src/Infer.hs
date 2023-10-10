
module Infer
  ( Infer(..), runInfer, TypeError
  , Subst
  , instantiateScheme, canonicalizeScheme
  , subTrans, subStack, subElem, subNumeric
  )
  where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Text.Printf (printf)
import qualified Data.Map as Map

import Types
  ( Scheme(..), makeScheme
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Numeric(..)
  , Contents(..)
  , SVar(..)
  , EVar(..)
  , NVar(..)
  )

----------------------------------------------------------------------
-- instantiateScheme, canonicalizeScheme

instantiateScheme :: Scheme -> Infer Trans
instantiateScheme (Scheme svars evars nvars ty) = do
  s <- Map.fromList <$> sequence [ do y <- FreshS; pure (x,S_Var y) | x <- svars ]
  e <- Map.fromList <$> sequence [ do y <- FreshE; pure (x,E_Var y) | x <- evars ]
  n <- Map.fromList <$> sequence [ do y <- FreshN; pure (x,N_Var y) | x <- nvars ]
  let sub = Subst { s, e, n }
  pure (subTrans sub ty)

canonicalizeScheme :: Scheme -> Trans
canonicalizeScheme (Scheme svars evars nvars ty) = do
  let s = Map.fromList [ (x,S_Var (SVar n)) | (x,n) <- zip svars [0.. ] ]
  let i = Map.size s
  let e = Map.fromList [ (x,E_Var (EVar n)) | (x,n) <- zip evars [i.. ] ]
  let j = Map.size s + Map.size e
  let n = Map.fromList [ (x,N_Var (NVar n)) | (x,n) <- zip nvars [j.. ] ]
  let sub = Subst { s, e, n }
  subTrans sub ty

----------------------------------------------------------------------
-- Infer

instance Functor Infer where fmap = liftM
instance Applicative Infer where pure = Return; (<*>) = ap
instance Monad Infer where (>>=) = Bind

data Infer a where
  Return :: a -> Infer a
  Bind :: Infer a -> (a -> Infer b) -> Infer b
  Message :: String -> Infer ()
  SubStack :: SVar -> Stack -> Infer ()
  SubElem :: EVar -> Elem -> Infer ()
  SubNumeric :: NVar -> Numeric -> Infer ()
  Nope :: String -> Infer a
  CurrentSub :: Infer Subst
  FreshS :: Infer SVar
  FreshE :: Infer EVar
  FreshN :: Infer NVar

type InfRes a = IO (Either TypeError a)

runInfer :: Infer Trans -> InfRes Trans
runInfer inf0 = loop state0 inf0 k0
  where
    k0 :: Trans -> State -> InfRes Trans
    k0 ty0 State{subst} = do
      let ty1 = subTrans subst ty0
      let ty2 = canonicalizeScheme (makeScheme ty1)
      pure (Right ty2)

    loop :: State -> Infer a -> (a -> State -> InfRes b) -> InfRes b
    loop s inf k = case inf of
      Return x -> do
        k x s
      Bind m f -> do
        loop s m $ \a s -> loop s (f a) k
      Message mes -> do
        printf "*Message: %s\n" mes
        k () s
      SubStack v stack -> do
        let State{subst} = s
        subst' <- extendSubstStack subst v stack
        k () s { subst = subst' }
      SubElem v elem -> do
        let State{subst} = s
        subst' <- extendSubstElem subst v elem
        k () s { subst = subst' }
      SubNumeric v num -> do
        let State{subst} = s
        subst' <- extendSubstNumeric subst v num
        k () s { subst = subst' }
      Nope message -> do
        pure (Left (TypeError (printf "Nope: %s" message)))
      CurrentSub -> do
        let State{subst} = s
        k subst s
      FreshS -> do
        let State{u} = s
        let x = SVar u
        k x s { u = u + 1 }
      FreshE -> do
        let State{u} = s
        let x = EVar u
        k x s { u = u + 1 }
      FreshN -> do
        let State{u} = s
        let x = NVar u
        k x s { u = u + 1 }

data State = State { subst :: Subst, u :: Int }

state0 :: State
state0 = State { subst = subst0, u = 0 }

----------------------------------------------------------------------
-- sub*

subTrans :: Subst -> Trans -> Trans
subTrans sub = \case
  T_Trans m1 m2 ->
    T_Trans (subMachine sub m1) (subMachine sub m2)

subMachine :: Subst -> Machine -> Machine
subMachine sub = \case
  Machine{stack} ->
    Machine { stack = subStack sub stack }

subStack :: Subst -> Stack -> Stack
subStack sub = loop
  where
    loop :: Stack -> Stack
    loop = \case
      S_Cons s v ->
        S_Cons (loop s) (subElem sub v)
      stack@(S_Var var) ->
        case applySubstS sub var of
          Nothing -> stack
          Just replacement -> replacement
      stack@S_Skolem{} ->
        stack

subElem :: Subst -> Elem -> Elem
subElem sub = \case
  E_Numeric n -> E_Numeric (subNumeric sub n)
  elem@(E_Var var) ->
    case applySubstE sub var of
      Nothing -> elem
      Just replacement -> replacement

subNumeric :: Subst -> Numeric -> Numeric
subNumeric sub = \case
  N_Number -> N_Number
  N_Address c -> N_Address (subContents sub c)
  numeric@(N_Var var) ->
    case applySubstN sub var of
      Nothing -> numeric
      Just replacement -> replacement

subContents :: Subst -> Contents -> Contents
subContents sub = \case
  C_Char -> C_Char
  C_Elem e -> C_Elem (subElem sub e)
  C_Code t -> C_Code (subTrans sub t)

----------------------------------------------------------------------
-- Subst

data Subst = Subst
  { s :: Map SVar Stack
  , e :: Map EVar Elem
  , n :: Map NVar Numeric
  }

applySubstS :: Subst -> SVar -> Maybe Stack
applySubstS Subst {s} x = Map.lookup x s

applySubstE :: Subst -> EVar -> Maybe Elem
applySubstE Subst {e} x = Map.lookup x e

applySubstN :: Subst -> NVar -> Maybe Numeric
applySubstN Subst {n} x = Map.lookup x n

instance Show Subst where
  show Subst{s,e} =
    unwords $
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList s ] ++
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList e ]

subst0 :: Subst
subst0 = Subst { s = Map.empty, e = Map.empty, n = Map.empty }

extendSubstStack :: Subst -> SVar -> Stack -> IO Subst
extendSubstStack Subst{s,e,n} key replacement = do
  let sub1 = Subst { s = Map.singleton key replacement
                   , e = Map.empty
                   , n = Map.empty
                   }
  pure $ Subst { s = Map.insert key replacement (Map.map (subStack sub1) s)
               , e = Map.map (subElem sub1) e
               , n = Map.map (subNumeric sub1) n
               }

extendSubstElem :: Subst -> EVar -> Elem -> IO Subst
extendSubstElem Subst{s,e,n} key replacement = do
  let sub1 = Subst { e = Map.singleton key replacement
                   , s = Map.empty
                   , n = Map.empty
                   }
  pure $ Subst { s = Map.map (subStack sub1) s
               , e = Map.insert key replacement (Map.map (subElem sub1) e)
               , n = Map.map (subNumeric sub1) n
               }

extendSubstNumeric :: Subst -> NVar -> Numeric -> IO Subst
extendSubstNumeric Subst{s,e,n} key replacement = do
  let sub1 = Subst { e = Map.empty
                   , s = Map.empty
                   , n = Map.singleton key replacement
                   }
  pure $ Subst { s = Map.map (subStack sub1) s
               , e = Map.map (subElem sub1) e
               , n = Map.insert key replacement (Map.map (subNumeric sub1) n)
               }

data TypeError = TypeError String -- TODO: needs fleshing out!

deriving instance Show TypeError
