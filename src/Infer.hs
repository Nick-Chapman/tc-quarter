
module Infer
  ( Infer(..), runInfer, TypeError
  , Subst
  , instantiateScheme, canonicalizeScheme
  , subTrans, subStack, subElem
  )
  where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Data.Set (Set)
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Types
  ( Scheme(..)
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Numeric(..)
  , Contents(..)
  , SVar(..), svarsOfStack
  , EVar(..), evarsOfElem
  )

----------------------------------------------------------------------
-- instantiateScheme, canonicalizeScheme

instantiateScheme :: Scheme -> Infer Trans
instantiateScheme (Scheme svars evars ty) = do
  s <- Map.fromList <$> sequence [ do y <- FreshS; pure (x,S_Var y) | x <- svars ]
  e <- Map.fromList <$> sequence [ do y <- FreshE; pure (x,E_Var y) | x <- evars ]
  let sub = Subst { s , e }
  pure (subTrans sub ty)

canonicalizeScheme :: Scheme -> Trans
canonicalizeScheme (Scheme svars evars ty) = do
  let s = Map.fromList [ (x,S_Var (SVar n)) | (x,n) <- zip svars [0.. ] ]
  let i = Map.size s
  let e = Map.fromList [ (x,E_Var (EVar n)) | (x,n) <- zip evars [i.. ] ]
  let sub = Subst { s , e }
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
  Nope :: String -> Infer a
  CurrentSub :: Infer Subst
  FreshS :: Infer SVar
  FreshE :: Infer EVar

type InfRes a = IO (Either TypeError a)

runInfer :: Infer Trans -> InfRes Trans
runInfer inf0 = loop state0 inf0 k0
  where
    k0 :: Trans -> State -> InfRes Trans
    k0 ty State{subst} = do
      let ty' = subTrans subst ty
      pure (Right ty')

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
        --printf "SubStack: %s -> %s\n" (show v) (show stack)
        let State{subst} = s
        subst' <- extendSubstStack subst v stack
        --printf "subst: %s\n" (show subst')
        checkInvariant subst'
        k () s { subst = subst' }
      SubElem v elem -> do
        --printf "SubElem: %s -> %s\n" (show v) (show elem)
        let State{subst} = s
        subst' <- extendSubstElem subst v elem
        --printf "subst: %s\n" (show subst')
        checkInvariant subst'
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
  E_XT t -> E_XT (subTrans sub t)
  elem@(E_Var var) ->
    case applySubstE sub var of
      Nothing -> elem
      Just replacement -> replacement

subNumeric :: Subst -> Numeric -> Numeric
subNumeric sub = \case
  N_Number -> N_Number
  N_Address c -> N_Address (subContents sub c)

subContents :: Subst -> Contents -> Contents
subContents sub = \case
  C_Char -> C_Char
  C_Elem e -> C_Elem (subElem sub e)

----------------------------------------------------------------------
-- Subst

data Subst = Subst
  { s :: Map SVar Stack
  , e :: Map EVar Elem
  }

applySubstS :: Subst -> SVar -> Maybe Stack
applySubstS Subst {s} x = Map.lookup x s

applySubstE :: Subst -> EVar -> Maybe Elem
applySubstE Subst {e} x = Map.lookup x e

domainS :: Subst -> Set SVar
domainS Subst{s} = Set.fromList $ Map.keys s

rangeS :: Subst -> Set SVar
rangeS Subst{s} = Set.unions [ Set.fromList $ svarsOfStack v | v <- Map.elems s ]

domainE :: Subst -> Set EVar
domainE Subst{e} = Set.fromList $ Map.keys e

rangeE :: Subst -> Set EVar
rangeE Subst{e} = Set.unions [ Set.fromList $ evarsOfElem v | v <- Map.elems e ]

checkInvariant :: Subst -> IO ()
checkInvariant sub = do
  let sd = domainS sub
  let sr = rangeS sub
  let si = sd `Set.intersection` sr
  let ed = domainE sub
  let er = rangeE sub
  let ei = ed `Set.intersection` er
  if Set.null si && Set.null ei then pure () else do
    printf "invariant fails\n"
    printf "- subst: %s\n" (show sub)
    printf "- domainS: %s\n" (show sd)
    printf "- rangeS: %s\n" (show sr)
    printf "- intersectS: %s\n" (show si)
    printf "- domainE: %s\n" (show ed)
    printf "- rangeE: %s\n" (show er)
    printf "- intersectE: %s\n" (show ei)
    undefined

instance Show Subst where
  show Subst{s,e} =
    unwords $
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList s ] ++
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList e ]

subst0 :: Subst
subst0 = Subst { s = Map.empty, e = Map.empty }

extendSubstStack :: Subst -> SVar -> Stack -> IO Subst
extendSubstStack sub0@Subst{s,e} key replacement = do
  checkSubstStackOk sub0 key replacement
  let sub1 = Subst { s = Map.singleton key replacement, e = Map.empty }
  pure $ Subst { s = Map.insert key replacement (Map.map (subStack sub1) s)
               , e = Map.map (subElem sub1) e }

extendSubstElem :: Subst -> EVar -> Elem -> IO Subst
extendSubstElem sub0@Subst{s,e} key replacement = do
  checkSubstElemOk sub0 key replacement
  let sub1 = Subst { e = Map.singleton key replacement, s = Map.empty }
  pure $ Subst { s = Map.map (subStack sub1) s
               , e = Map.insert key replacement (Map.map (subElem sub1) e) }


checkSubstStackOk :: Subst -> SVar -> Stack -> IO ()
checkSubstStackOk sub key replacement = do
  if (key `Set.member` dom) then report else do
  if (not (Set.null (dom `Set.intersection` Set.fromList (svarsOfStack replacement)))) then report else do
  pure ()
    where
      dom = domainS sub
      report = do
        printf "checkSubstStackOk fails\n"
        printf "- subst: %s\n" (show sub)
        printf "- domain: %s\n" (show dom)
        printf "- key: %s\n" (show key)
        printf "- replacement: %s\n" (show replacement)
        undefined

checkSubstElemOk :: Subst -> EVar -> Elem -> IO ()
checkSubstElemOk sub key replacement = do
  if (key `Set.member` dom) then report else do
  if (not (Set.null (dom `Set.intersection` Set.fromList (evarsOfElem replacement)))) then report else do
  pure ()
    where
      dom = domainE sub
      report = do
        printf "checkSubstElemOk fails\n"
        printf "- subst: %s\n" (show sub)
        printf "- domain: %s\n" (show dom)
        printf "- key: %s\n" (show key)
        printf "- replacement: %s\n" (show replacement)
        undefined

data TypeError = TypeError String -- TODO: needs fleshing out!

deriving instance Show TypeError
