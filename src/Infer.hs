
module Infer
  ( Infer(..)
  , runInfer, reasonToInfer
  , TypeError(..)
  , Subst
  , instantiateScheme, canonicalizeScheme
  , subTrans, subStack, subElem, subContents
  , freshStack, freshElem, freshContents
  )
  where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Text.Printf (printf)
import qualified Data.Map as Map

import Types
  ( Scheme(..)
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Contents(..)
  , SVar(..)
  , EVar(..)
  , CVar(..)
  )

import Execution (Loc)

----------------------------------------------------------------------
-- fresh

freshStack :: Infer Stack
freshStack = S_Var <$> FreshS

freshElem :: Infer Elem
freshElem = E_Var <$> FreshE

freshContents :: Infer Contents
freshContents = C_Var <$> FreshC

----------------------------------------------------------------------
-- instantiateScheme, canonicalizeScheme

instantiateScheme :: Scheme -> Infer Trans
instantiateScheme (Scheme svars evars cvars ty) = do
  s <- Map.fromList <$> sequence [ do y <- FreshS; pure (x,S_Var y) | x <- svars ]
  e <- Map.fromList <$> sequence [ do y <- FreshE; pure (x,E_Var y) | x <- evars ]
  c <- Map.fromList <$> sequence [ do y <- FreshC; pure (x,C_Var y) | x <- cvars ]
  let sub = Subst { s, e, c = c }
  pure (subTrans sub ty)

canonicalizeScheme :: Scheme -> Trans
canonicalizeScheme (Scheme svars evars cvars ty) = do
  let s = Map.fromList [ (x,S_Var (SVar n)) | (x,n) <- zip svars [0.. ] ]
  let i = Map.size s
  let e = Map.fromList [ (x,E_Var (EVar n)) | (x,n) <- zip evars [i.. ] ]
  let j = Map.size s + Map.size e
  let c = Map.fromList [ (x,C_Var (CVar n)) | (x,n) <- zip cvars [j.. ] ]
  let sub = Subst { s, e, c }
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
  SubContents :: CVar -> Contents -> Infer ()
  Nope :: String -> Infer ()
  CurrentSub :: Infer Subst
  FreshS :: Infer SVar -- TODO: combine 3x Fresh ops
  FreshE :: Infer EVar
  FreshC :: Infer CVar
  Reason :: Loc -> String -> Infer a -> Infer a

type InfRes a = IO ([TypeError],a)

reasonToInfer :: Loc -> String -> Infer a -> Infer a
reasonToInfer = Reason

runInfer :: Loc -> Int -> Infer a -> InfRes (Int,Subst,a) -- TODO: be more principled!
runInfer loc u0 inf0 = loop (state0 u0 loc) inf0 k0
  where
    k0 :: a -> State -> InfRes (Int,Subst,a)
    k0 a State{subst,u,errs} = do
      pure (errs,(u,subst,a))

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
      SubContents v c -> do
        let State{subst} = s
        subst' <- extendSubstContents subst v c
        k () s { subst = subst' }
      Nope message -> do
        let State{errs,reason=(loc,why)} = s
        let err = TypeError {loc,why,message}
        k () s { errs = err : errs }
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
      FreshC -> do
        let State{u} = s
        let x = CVar u
        k x s { u = u + 1 }
      Reason loc why m -> do
        loop s { reason = (loc,why) } m k

data State = State
  { subst :: Subst
  , u :: Int
  , errs :: [TypeError]
  , reason :: (Loc,String)
  }

state0 :: Int -> Loc -> State
state0 u loc = State { subst = subst0, u, errs = [], reason = (loc,"top") }

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
      S_Unknown -> S_Unknown
      stack@(S_Var var) ->
        case applySubstS sub var of
          Nothing -> stack
          Just replacement -> replacement


subElem :: Subst -> Elem -> Elem
subElem sub = \case
  E_Number -> E_Number
  E_Address c -> E_Address (subContents sub c)
  E_Unknown -> E_Unknown
  elem@(E_Var var) ->
    case applySubstE sub var of
      Nothing -> elem
      Just replacement -> replacement

subContents :: Subst -> Contents -> Contents
subContents sub = \case
  C_Char -> C_Char
  C_Elem e -> C_Elem (subElem sub e)
  C_Code t -> C_Code (subTrans sub t)
  c@(C_Var var) ->
    case applySubstC sub var of
      Nothing -> c
      Just replacement -> replacement

----------------------------------------------------------------------
-- Subst

data Subst = Subst
  { s :: Map SVar Stack
  , e :: Map EVar Elem
  , c :: Map CVar Contents
  }

applySubstS :: Subst -> SVar -> Maybe Stack
applySubstS Subst {s} x = Map.lookup x s

applySubstE :: Subst -> EVar -> Maybe Elem
applySubstE Subst {e} x = Map.lookup x e

applySubstC :: Subst -> CVar -> Maybe Contents
applySubstC Subst {c} x = Map.lookup x c

instance Show Subst where
  show Subst{s,e,c} =
    unwords $
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList s ] ++
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList e ] ++
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList c ]

subst0 :: Subst
subst0 = Subst { s = Map.empty, e = Map.empty, c = Map.empty }

extendSubstStack :: Subst -> SVar -> Stack -> IO Subst
extendSubstStack Subst{s,e,c} key replacement = do
  let sub1 = Subst { s = Map.singleton key replacement
                   , e = Map.empty
                   , c = Map.empty
                   }
  pure $ Subst { s = Map.insert key replacement (Map.map (subStack sub1) s)
               , e = Map.map (subElem sub1) e
               , c = Map.map (subContents sub1) c
               }

extendSubstElem :: Subst -> EVar -> Elem -> IO Subst
extendSubstElem Subst{s,e,c} key replacement = do
  let sub1 = Subst { e = Map.singleton key replacement
                   , s = Map.empty
                   , c = Map.empty
                   }
  pure $ Subst { s = Map.map (subStack sub1) s
               , e = Map.insert key replacement (Map.map (subElem sub1) e)
               , c = Map.map (subContents sub1) c
               }

extendSubstContents :: Subst -> CVar -> Contents -> IO Subst
extendSubstContents Subst{s,e,c} key replacement = do
  let sub1 = Subst { e = Map.empty
                   , s = Map.empty
                   , c = Map.singleton key replacement
                   }
  pure $ Subst { s = Map.map (subStack sub1) s
               , e = Map.map (subElem sub1) e
               , c = Map.insert key replacement (Map.map (subContents sub1) c)
               }

data TypeError = TypeError
  { loc :: Loc
  , why :: String
  , message :: String
  }

instance Show TypeError where
  show TypeError{loc,why,message} =
    printf "%s (%s) : %s" (show loc) why message
