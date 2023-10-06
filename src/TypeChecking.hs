
module TypeChecking
  ( tcMachine, extra
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Text.Printf (printf)

import Data.Set (Set)
import qualified Data.Set as Set

import Execution
  ( Slot(..), Addr(..), Value(..), Numb, seeChar, offsetAddr, slotSize
  , Prim(..)
  )

import qualified Execution as X
  ( Machine(..)
  )

extra :: String
extra = unlines
  [ ":2 ^O?> ;"
  , ":3 ^O?> ^O?> ;"
  ]

tcMachine :: X.Machine -> IO ()
tcMachine X.Machine{dispatchTable=dt,mem} = do
  let _all = [ x | (_,x) <- Map.toList userQDefs ]
  mapM_ tcDef _all -- "'~23"
  where
    tcDef :: Char -> IO ()
    tcDef c = do
      let slots = slotsForDef c
      printf "%s : %s\n" (seeChar c) (unwords (map seeSlot slots))

      either <- runInfer (tcSlotsExec slots)
      case either of
        Left e ->
          printf "ERROR: %s\n" (show e)

        Right ty -> do
          printf ":: %s\n" (show ty)

    look :: Addr -> Slot
    look a = maybe undefined id (Map.lookup a mem)

    slotsForDef :: Char -> [Slot]
    slotsForDef c = do
      let a = maybe undefined id (Map.lookup c dt)
      collectSlots [] a

    collectSlots :: [Slot] -> Addr -> [Slot]
    collectSlots acc a = do
      let slot = look a
      let a' = offsetAddr (slotSize slot) a
      case slot of
        SlotRet -> reverse (slot:acc)
        _ -> collectSlots (slot:acc) a'

    -- special case address which are in the dispatchTable
    seeSlot :: Slot -> String
    seeSlot = \case
      SlotCall (AN n) -> seeUserQ n
      SlotLit v -> printf "#%s" (seeValue v)
      slot -> show slot

    seeValue :: Value -> String
    seeValue = \case
      VA (AN n) -> seeUserQ n
      v -> show v

    seeUserQ :: Numb -> String
    seeUserQ n =
      case Map.lookup n userQDefs of
        Just c -> seeChar c
        Nothing -> show n

    -- Reverse mapping of user-generated defs
    userQDefs :: Map Numb Char
    userQDefs = Map.fromList [ (n,c) | (c,AN n) <- Map.toList dt ]



tcSlotsExec :: [Slot] -> Infer Effect
tcSlotsExec = \case
  [] -> noEffect
  slot1:slots -> do
    e1 <- tcSlotExec slot1
    e2 <- tcSlotsExec slots
    sub <- CurrentSub
    let e1' = subEffect sub e1
    let e2' = subEffect sub e2
    composeEffect e1' e2'

noEffect :: Infer Effect
noEffect = do
  x <- Fresh
  let s = TS_var x
  let m = TM { stack = s }
  pure (TE_effect m m)

composeEffect :: Effect -> Effect -> Infer Effect
composeEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m2 m3
      pure (TE_effect m1 m4)

tcSlotExec :: Slot -> Infer Effect
tcSlotExec slot = case slot of
  SlotCall a -> tcAddrExec a
  SlotRet -> noEffect
  SlotLit{} -> nope
  SlotChar{} -> nope
  SlotEntry{} -> nope
  SlotString{} -> nope
  where
    nope = Nope (printf "tcSlotExec: %s" (show slot))


tcAddrExec :: Addr -> Infer Effect
tcAddrExec a = case a of
  AP p -> tcPrimExec p
  AN{} -> nope
  APE{} -> nope
  AS{} -> nope
  AH -> nope
  where
    nope = Nope (printf "tcAddrExec: %s" (show a))


schemeOfPrim :: Prim -> Maybe Scheme
schemeOfPrim = \case

  Key -> scheme $ s1 ~~> (s1 ~ num)

  Dispatch -> scheme $ (s1 ~ num) ~~> (s1 ~ xt (TS_exists "S1" ~~> TS_exists "S2"))

  CompileComma -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> s1

  Over -> scheme $ (s1 ~ x1 ~ x2) ~~> (s1 ~ x1 ~ x2 ~ x1)
    where
      x1 = num -- Should be polymorphic. -- need polymorphic elem types
      x2 = num

  _ -> Nothing

  where
    scheme = Just . makeScheme

    (~~>) stack1 stack2 =
      TE_effect (TM stack1) (TM stack2)

    (~) stack elem = TS_cons stack elem

    xt = T_addr . TA_xt
    num = T_num

    s1 = mkVar 1
    s2 = mkVar 2
    s3 = mkVar 3

    mkVar = TS_var . TVar


makeScheme :: Effect -> Scheme
makeScheme e = Scheme (varsOfEffect e) e

tcPrimExec :: Prim -> Infer Effect
tcPrimExec prim =
  case schemeOfPrim prim of
    Nothing -> Nope (printf "tcPrimExec: %s" (show prim))
    Just scheme -> instantiateScheme scheme

instantiateScheme :: Scheme -> Infer Effect
instantiateScheme (Scheme vars ty) = do
  bs <- sequence [ do y <- Fresh; pure (x,TS_var y) | x <- Set.toList vars]
  let sub = Subst (Map.fromList bs)
  pure (subEffect sub ty)

----------------------------------------------------------------------
-- Language of Types

data Scheme
  = Scheme (Set TVar) Effect

-- Type of a machine tranformation -- what occurs during execution
data Effect
  = TE_effect Machine Machine

-- Type of a machine state
data Machine = TM
  { stack :: Stack
  -- TODO: we also need the return stack
  -- TODO: and we need info relating to here/compiling
  }

-- Type of a stack of elements
data Stack
  = TS_cons Stack Elem
--  | TS_empty
  | TS_var TVar
  | TS_exists String -- existential state. you dont get to pick! skolem?

data Elem -- the type of a 16-bit value, or cell. things which can be stack items
  = T_num -- 16 bit numeric value; may be a char/bool
  | T_addr Pointer -- 16 bit address of something -- TODO: extra indirection buy anything?
--  | T_var Int -- TODO, need this

data Pointer -- the type of the slot at an address
  = TA_xt Effect -- slot containg XT with an effect
--  | TA_call Effect -- ( s -- s' ) slot containing call with effect
--  | TA_char -- char* -- slot containing a char
--  | TA_lit Elem -- T* -- slot containing a 16-bit value
  -- No variable here!

----------------------------------------------------------------------
-- Show

instance Show Effect where
  show = \case
    TE_effect m1 m2 ->
      printf "(%s -- %s)" (show m1) (show m2)

instance Show Machine where
  show = \case
    TM{stack} -> show stack

instance Show Stack where
  show = \case
    TS_cons s v -> printf "%s %s" (show s) (show v)
    TS_var n -> show n
    TS_exists x -> x

instance Show Elem where
  show = \case
    T_num{} -> "N"
    T_addr a -> show a

instance Show Pointer where
  show = \case
    TA_xt e -> printf "XT%s" (show e)

instance Show TVar where
  show (TVar n) = printf "%s" (show n)

----------------------------------------------------------------------
-- varsOf*

varsOfEffect :: Effect -> Set TVar
varsOfEffect = \case
  TE_effect m1 m2 -> varsOfMachine m1 `Set.union` varsOfMachine m2

varsOfMachine :: Machine -> Set TVar
varsOfMachine = \case
  TM{stack} -> varsOfStack stack

varsOfStack :: Stack -> Set TVar
varsOfStack = \case
  TS_cons s v -> varsOfStack s `Set.union` varsOfValue v
  TS_var x -> Set.singleton x
  TS_exists{} -> Set.empty

varsOfValue :: Elem -> Set TVar
varsOfValue = \case
  T_num -> Set.empty
  T_addr a -> varsOfPointer a

varsOfPointer :: Pointer -> Set TVar
varsOfPointer = \case
  TA_xt e -> varsOfEffect e

----------------------------------------------------------------------
-- sub*

subEffect :: Subst -> Effect -> Effect
subEffect sub = \case
    TE_effect m1 m2 ->
      TE_effect (subMachine sub m1) (subMachine sub m2)

subMachine :: Subst -> Machine -> Machine
subMachine sub = \case
  TM{stack} -> TM { stack = subStack sub stack }

subStack :: Subst -> Stack -> Stack
subStack sub = loop
  where
    loop :: Stack -> Stack
    loop = \case
      TS_cons s v ->
        TS_cons (loop s) (subValue sub v)
      stack@(TS_var var) ->
        case applySubst sub var of
          Nothing -> stack
          Just replacement -> replacement
      stack@TS_exists{} ->
        stack

subValue :: Subst -> Elem -> Elem
subValue sub = \case
  T_num -> T_num
  T_addr a -> T_addr (subPointer sub a)

subPointer :: Subst -> Pointer -> Pointer
subPointer sub = \case
  TA_xt e -> TA_xt (subEffect sub e)

----------------------------------------------------------------------
-- unify*

unifyEffect :: Effect -> Effect -> Infer ()
unifyEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m1 m3
      unifyMachine m2 m4

unifyMachine :: Machine -> Machine -> Infer ()
unifyMachine m1 m2 = do
  case (m1,m2) of
    (TM{stack=s1},TM{stack=s2}) ->
      unifyStack s1 s2

unifyStack :: Stack -> Stack -> Infer ()
unifyStack s1 s2 =
  case (s1,s2) of

    (TS_var x1, stack@(TS_var x2)) ->
      if x1==x2 then pure () else InfSubst x1 stack

    (TS_var x, stack) ->
      if x `elem` varsOfStack stack then cyclic else InfSubst x stack

    (stack, TS_var x) ->
      if x `elem` varsOfStack stack then cyclic else InfSubst x stack

    (TS_cons s1 v1, TS_cons s2 v2) -> do
      unifyStack s1 s2
      unifyValue v1 v2

    (TS_cons{}, _) -> Nope "cons/?"
    (_, TS_cons{}) -> Nope "?/cons"
    (TS_exists x1, TS_exists x2) -> if (x1 == x2) then pure () else Nope "?/?"

  where
    cyclic = Nope (printf "cyclic: %s =!= %s" (show s1) (show s2))

unifyValue :: Elem -> Elem -> Infer ()
unifyValue v1 v2 =
  case (v1,v2) of
    (T_num,T_num) -> pure ()
    (T_num,T_addr{}) -> Nope "num/addr"
    (T_addr{},T_num) -> Nope "addr/num"
    (T_addr a1, T_addr a2) -> unifyPointer a1 a2

unifyPointer :: Pointer -> Pointer -> Infer ()
unifyPointer a1 a2 =
  case (a1,a2) of
    (TA_xt e1, TA_xt e2) -> unifyEffect e1 e2

----------------------------------------------------------------------
-- Infer

instance Functor Infer where fmap = liftM
instance Applicative Infer where pure = InfReturn; (<*>) = ap
instance Monad Infer where (>>=) = InfBind

data Infer a where
  InfReturn :: a -> Infer a
  InfBind :: Infer a -> (a -> Infer b) -> Infer b
  InfSubst :: TVar -> Stack -> Infer ()
  Nope :: String -> Infer a
  CurrentSub :: Infer Subst
  Fresh :: Infer TVar


type InfRes a = IO (Either TypeError a)

runInfer :: Infer Effect -> InfRes Effect
runInfer inf0 = loop state0 inf0 k0
  where
    k0 :: Effect -> State -> InfRes Effect
    k0 ty State{subst} = do
      let ty' = subEffect subst ty
      pure (Right ty')

    loop :: State -> Infer a -> (a -> State -> InfRes b) -> InfRes b
    loop s inf k = case inf of
      InfReturn x -> do
        k x s
      InfBind m f -> do
        loop s m $ \a s -> loop s (f a) k
      InfSubst v stack -> do
        --printf "%s -> %s\n" (show v) (show stack)
        let State{subst} = s
        let subst' = extendSubst subst v stack
        --printf "subst: %s\n" (show subst')
        checkInvariant subst'
        k () s { subst = subst' }
      Nope message -> do
        pure (Left (TypeError (printf "Nope: %s" message)))
      CurrentSub -> do
        let State{subst} = s
        k subst s
      Fresh -> do
        let State{u} = s
        let x = TVar u
        k x s { u = u + 1 }

data State = State { subst :: Subst, u :: Int }

state0 :: State
state0 = State { subst = subst0, u = 0 }

----------------------------------------------------------------------
-- Subst

data Subst = Subst (Map TVar Stack) -- TODO: Need 2nd map for non stack vars

applySubst :: Subst -> TVar -> Maybe Stack
applySubst (Subst m) x = Map.lookup x m

domain :: Subst -> Set TVar
domain (Subst m) = Set.fromList $ Map.keys m

range :: Subst -> Set TVar
range (Subst m) = Set.unions [ varsOfStack s | s <- Map.elems m ]

checkInvariant :: Subst -> IO ()
checkInvariant sub = do
  let d = domain sub
  let r = range sub
  let i = d `Set.intersection` r
  if Set.null i then pure () else do
    printf "subst: %s\n" (show sub)
    printf "domain: %s\n" (show d)
    printf "range: %s\n" (show r)
    printf "intersect: %s\n" (show i)
    error "invariant fails"

instance Show Subst where
  show (Subst m) =
    unwords [ printf "%s: %s," (show v) (show s)
            | (v,s) <- Map.toList m ]

subst0 :: Subst
subst0 = Subst Map.empty

extendSubst :: Subst -> TVar -> Stack -> Subst
extendSubst (Subst m) key replacement = do

  let g = Subst (Map.singleton key replacement)
  let mShifted = Map.map (subStack g) m
  Subst (Map.insert key replacement mShifted)

-- TODO: need a 2nd type for vars which can bind to value-types
-- How name things to make it clear when have value/stack vars ?

data TVar = TVar Int -- currently only stacks can be variable
  deriving (Eq,Ord)

data TypeError = TypeError String

deriving instance Show TypeError

