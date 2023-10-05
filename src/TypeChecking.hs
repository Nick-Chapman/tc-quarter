
module TypeChecking
  ( seeFinalMachine
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Text.Printf (printf)

import Execution
  ( Machine(..)
  , Slot(..), Addr(..), Value(..), Numb, seeChar, offsetAddr, slotSize
  , Prim(..)
  )

seeFinalMachine :: Machine -> String
seeFinalMachine m@Machine{mem=_mem} =
  unlines [ dumpDispatchTable m
          , tcSomething m
          ]

dumpDispatchTable :: Machine -> String
dumpDispatchTable Machine{dispatchTable=dt,mem} =
  unlines
  [ printf "%s : %s" (seeChar c) (unwords (map seeSlot slots))
  | (n,c) <- Map.toList userQDefs
  -- , c == '~' -- TODO: temp. just see the def of ~
  , let slots = collectDef [] (AN n)
  ]
  where
    collectDef :: [Slot] -> Addr -> [Slot]
    collectDef acc a =
      case Map.lookup a mem of
        Nothing -> error (show ("collectDef/addr",a))
        Just slot -> do
          let a' = offsetAddr (slotSize slot) a
          case slot of
            SlotRet -> reverse (slot:acc)
            _ -> collectDef (slot:acc) a'

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


tcSomething :: Machine -> String
tcSomething Machine{dispatchTable=dt,mem} = do

  let aTilda = maybe undefined id (Map.lookup '~' dt) -- that something is the ~ definition
  let slots = collectSlots [] aTilda
  seeRes (runInfer (tcSlotsExec slots))

  where

    seeRes :: Either TypeError (TyEffect,Subst) -> String
    seeRes = \case
      Left e ->
        printf "~ :: ERROR: %s" (show e) -- TODO: use coorrect name
      Right (eff,subst) -> do
        let sub = useSubst subst
        unlines [ printf "~ :: %s" (show eff)
                , printf "SUB: %s" (show subst)
                , printf "APP: %s" (show (subEffect sub eff))
                ]

    look :: Addr -> Slot
    look a = maybe undefined id (Map.lookup a mem)

    collectSlots :: [Slot] -> Addr -> [Slot]
    collectSlots acc a = do
      let slot = look a
      let a' = offsetAddr (slotSize slot) a
      case slot of
        SlotRet -> reverse (slot:acc)
        _ -> collectSlots (slot:acc) a'


tcSlotsExec :: [Slot] -> Infer TyEffect
tcSlotsExec = \case
  [] -> pure effect0
  slot1:slots -> do
    e1 <- tcSlotExec slot1
    e2 <- tcSlotsExec slots
    sub <- CurrentSub
    let e1' = subEffect sub e1
    let e2' = subEffect sub e2
    composeEffect e1' e2'

tcSlotExec :: Slot -> Infer TyEffect
tcSlotExec slot = case slot of
  SlotCall a -> tcAddrExec a
  SlotRet -> pure effect0
  SlotLit{} -> nope
  SlotChar{} -> nope
  SlotEntry{} -> nope
  SlotString{} -> nope
  where
    nope = Nope (printf "tcSlotExec: %s" (show slot))

effect0 :: TyEffect
effect0 = TE_effect m m
  where
    m = TM { stack = s }
    s = TS_var (TVar 99) -- TODO: fresh

tcAddrExec :: Addr -> Infer TyEffect
tcAddrExec = \case
  AP p -> tcPrimExec p
  AN n -> undefined n
  APE p -> undefined p
  AS s -> undefined s
  AH -> undefined

-- TODO: primitives should be bound to type schemes!
-- which we instantiate with fresh vars at each use occurancex
tcPrimExec :: Prim -> Infer TyEffect
tcPrimExec = \case

  Key -> pure (TE_effect m1 m2)
    where
      m1 = TM { stack = s1 }
      m2 = TM { stack = TS_cons s1 T_num }
      s1 = TS_var (TVar 11) -- TODO : fresh

  Dispatch -> pure (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons s1 T_num }
      m2 = TM { stack = TS_cons s1 (T_addr (TA_xt e1)) }
      s1 = TS_var (TVar 22)
      e1 = TE_effect TM { stack = TS_exists "S1" } TM { stack = TS_exists "S2" }

  CompileComma -> pure (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons s1 (T_addr (TA_xt e1)) }
      m2 = TM { stack = s1 }
      s1 = TS_var (TVar 33)
      e1 = TE_effect TM { stack = TS_var (TVar 34) } TM { stack = TS_var (TVar 35) }

  p ->
    error (show ("tcPrimExec",p))


data TyEffect -- type of a machine effect (currently just stack effect)
  = TE_effect TyMachine TyMachine

composeEffect :: TyEffect -> TyEffect -> Infer TyEffect
composeEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m2 m3
      pure (TE_effect m1 m4)

subEffect :: Sub -> TyEffect -> TyEffect
subEffect sub = \case
    TE_effect m1 m2 ->
      TE_effect (subMachine sub m1) (subMachine sub m2)

unifyEffect :: TyEffect -> TyEffect -> Infer ()
unifyEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m1 m3
      unifyMachine m2 m4


data TyMachine = TM
  { stack :: TyStack -- currently just the type of the stack
  -- TODO: we also need the return statck
  -- TODO: and we need info relating to here/compiling
  }

subMachine :: Sub -> TyMachine -> TyMachine
subMachine sub = \case
  TM{stack} -> TM { stack = subStack sub stack }

unifyMachine :: TyMachine -> TyMachine -> Infer ()
unifyMachine m1 m2 = do
  case (m1,m2) of
    (TM{stack=s1},TM{stack=s2}) ->
      unifyStack s1 s2


data TyStack
  = TS_cons TyStack TyValue
--  | TS_empty
  | TS_var TVar
  | TS_exists String -- existential state. you dont get to pick! skolem?

subStack :: Sub -> TyStack -> TyStack
subStack sub = loop
  where
    loop :: TyStack -> TyStack
    loop = \case
      TS_cons s v ->
        TS_cons (loop s) (subValue sub v)
      stack@(TS_var var) ->
        case applySub sub var of
          Nothing -> stack
          Just replacement -> replacement
      stack@TS_exists{} ->
        stack

unifyStack :: TyStack -> TyStack -> Infer ()
unifyStack s1 s2 =
  case (s1,s2) of
    (TS_var var, stack) -> InfSubst var stack
    (stack, TS_var var) -> InfSubst var stack
    (TS_cons s1 v1, TS_cons s2 v2) -> do
      unifyStack s1 s2
      unifyValue v1 v2
    (TS_cons{}, _) -> Nope "cons/?"
    (_, TS_cons{}) -> Nope "?/cons"
    (TS_exists x1, TS_exists x2) -> if (x1 == x2) then pure () else Nope "?/?"


data TyValue -- the type of a 16-bit value, or cell. things which can be stack items
  = T_num -- 16 bit numeric value; may be a char/bool
  | T_addr TyAddr -- 16 bit address of something
--  | T_var Int

subValue :: Sub -> TyValue -> TyValue
subValue sub = \case
  T_num -> T_num
  T_addr a -> T_addr (subAddr sub a)

unifyValue :: TyValue -> TyValue -> Infer ()
unifyValue v1 v2 =
  case (v1,v2) of
    (T_num,T_num) -> pure ()
    (T_num,T_addr{}) -> Nope "num/addr"
    (T_addr{},T_num) -> Nope "addr/num"
    (T_addr a1, T_addr a2) -> unifyAddr a1 a2


data TyAddr -- the type of the slot at an address
  = TA_xt TyEffect -- slot containg XT with an effect
--  | TA_call TyEffect -- ( s -- s' ) slot containing call with effect
--  | TA_char -- char* -- slot containing a char
--  | TA_lit TyValue -- T* -- slot containing a 16-bit value
  -- No variable here!

subAddr :: Sub -> TyAddr -> TyAddr
subAddr sub = \case
  TA_xt e -> TA_xt (subEffect sub e)

unifyAddr :: TyAddr -> TyAddr -> Infer ()
unifyAddr a1 a2 =
  case (a1,a2) of
    (TA_xt e1, TA_xt e2) -> unifyEffect e1 e2


instance Show TyEffect where
  show = \case
    TE_effect m1 m2 ->
      printf "(%s -- %s)" (show m1) (show m2)

instance Show TyMachine where
  show = \case
    TM{stack} -> show stack

instance Show TyStack where
  show = \case
    TS_cons s v -> printf "%s %s" (show s) (show v)
    TS_var n -> show n
    TS_exists x -> x

instance Show TyValue where
  show = \case
    T_num{} -> "N"
    T_addr a -> show a

instance Show TyAddr where
  show = \case
    TA_xt e -> printf "XT%s" (show e)

instance Show TVar where
  show (TVar n) = printf "%s" (show n)


instance Functor Infer where fmap = liftM
instance Applicative Infer where pure = InfReturn; (<*>) = ap
instance Monad Infer where (>>=) = InfBind

data Infer a where
  InfReturn :: a -> Infer a
  InfBind :: Infer a -> (a -> Infer b) -> Infer b
  InfSubst :: TVar -> TyStack -> Infer ()
  Nope :: String -> Infer a
  CurrentSub :: Infer Sub

type InfRes a = Either TypeError (a,Subst)

runInfer :: Infer a -> InfRes a
runInfer inf0 = loop subst0 inf0 k0
  where
    k0 :: a -> Subst -> InfRes a
    k0 a s = Right (a,s)

    loop :: Subst -> Infer a -> (a -> Subst -> InfRes b) -> InfRes b
    loop s inf k = case inf of
      InfReturn x -> do
        k x s
      InfBind m f -> do
        loop s m $ \a s -> loop s (f a) k
      InfSubst v stack -> do
        k () (extendSubst s v stack)
      Nope s -> do
        Left (TypeError (printf "Nope: %s" s))
      CurrentSub -> do
        k (useSubst s) s


data Sub = Sub (TVar -> Maybe TyStack) -- functional rep

applySub :: Sub -> TVar -> Maybe TyStack
applySub (Sub f) = f


data Subst = Subst (Map TVar TyStack)

useSubst :: Subst -> Sub
useSubst (Subst m) = Sub (\v -> Map.lookup v m)

subst0 :: Subst
subst0 = Subst Map.empty

extendSubst :: Subst -> TVar -> TyStack -> Subst
extendSubst (Subst m) key replacement = do
  let g = Sub (\v -> if v==key then Just replacement else Nothing)
  let mShifted = Map.map (subStack g) m
  Subst (Map.insert key replacement mShifted)


data TVar = TVar Int -- currently only stacks can be variable
  deriving (Eq,Ord)

data TypeError = TypeError String

deriving instance Show TypeError
deriving instance Show Subst
