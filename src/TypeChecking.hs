
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
  ( Machine(..)
  , Slot(..), Addr(..), Value(..), Numb, seeChar, offsetAddr, slotSize
  , Prim(..)
  )

extra :: String
extra = unlines
  [ ":2 ^O?> ;"
  , ":3 ^O?> ^O?> ;"
  ]

tcMachine :: Machine -> IO ()
tcMachine Machine{dispatchTable=dt,mem} = do
  let _all = [ tcDef x | (_,x) <- Map.toList userQDefs ]
  mapM_ tcDef "'~23" -- _all
  where
    tcDef :: Char -> IO ()
    tcDef c = do
      let slots = slotsForDef c
      printf "%s : %s\n" (seeChar c) (unwords (map seeSlot slots))

      either <- runInfer (tcSlotsExec slots)
      case either of
        Left e ->
          printf "ERROR: %s\n" (show e)

        Right (eff,subst) -> do
          let sub = useSubst subst
          let ty = subEffect sub eff -- TODO:should return this
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


tcSlotsExec :: [Slot] -> Infer TyEffect
tcSlotsExec = \case
  [] -> noEffect
  slot1:slots -> do
    e1 <- tcSlotExec slot1
    e2 <- tcSlotsExec slots
    sub <- CurrentSub
    let e1' = subEffect sub e1
    let e2' = subEffect sub e2
    composeEffect e1' e2'

noEffect :: Infer TyEffect
noEffect = do
  x <- Fresh
  let s = TS_var x
  let m = TM { stack = s }
  pure (TE_effect m m)

composeEffect :: TyEffect -> TyEffect -> Infer TyEffect
composeEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m2 m3
      pure (TE_effect m1 m4)

tcSlotExec :: Slot -> Infer TyEffect
tcSlotExec slot = case slot of
  SlotCall a -> tcAddrExec a
  SlotRet -> noEffect
  SlotLit{} -> nope
  SlotChar{} -> nope
  SlotEntry{} -> nope
  SlotString{} -> nope
  where
    nope = Nope (printf "tcSlotExec: %s" (show slot))


tcAddrExec :: Addr -> Infer TyEffect
tcAddrExec a = case a of
  AP p -> tcPrimExec p
  AN{} -> nope
  APE{} -> nope
  AS{} -> nope
  AH -> nope
  where
    nope = Nope (printf "tcAddrExec: %s" (show a))


schemeOfPrim :: Prim -> Maybe TyScheme -- TODO: Make a static table of schemes
schemeOfPrim = \case

  Key -> scheme (TE_effect m1 m2)
    where
      m1 = TM { stack = s1 }
      m2 = TM { stack = TS_cons s1 T_num }

  Dispatch -> scheme (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons s1 T_num }
      m2 = TM { stack = TS_cons s1 (T_addr (TA_xt e1)) }
      e1 = TE_effect TM { stack = TS_exists "S1" } TM { stack = TS_exists "S2" }

  CompileComma -> scheme (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons s1 (T_addr (TA_xt e1)) }
      m2 = TM { stack = s1 }
      e1 = TE_effect TM { stack = s2 } TM { stack = s3 }

  Over -> scheme (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons (TS_cons s1 x1) x2 }
      m2 = TM { stack = TS_cons (TS_cons (TS_cons s1 x1) x2) x1 }
      x1 = T_num -- Should be polymorphic. -- need polymorphic elem types
      x2 = T_num -- Should be polymorphic

  _ -> Nothing

  where
    scheme = Just . makeScheme

    s1 = mkVar 1
    s2 = mkVar 2
    s3 = mkVar 3

    mkVar = TS_var . TVar


makeScheme :: TyEffect -> TyScheme
makeScheme e = TyScheme (varsOfEffect e) e

tcPrimExec :: Prim -> Infer TyEffect
tcPrimExec prim =
  case schemeOfPrim prim of
    Nothing -> Nope (printf "tcPrimExec: %s" (show prim))
    Just scheme -> instantiateScheme scheme

instantiateScheme :: TyScheme -> Infer TyEffect
instantiateScheme (TyScheme vars ty) = do
  bs <- sequence [ do y <- Fresh; pure (x,TS_var y) | x <- Set.toList vars]
  let m = Map.fromList bs
  let sub = Sub (\v -> Map.lookup v m)
  pure (subEffect sub ty)

----------------------------------------------------------------------
-- Language of Types

data TyScheme
  = TyScheme (Set TVar) TyEffect

-- TODO: rename Type - this is the main type!
data TyEffect -- type of a machine effect (currently just stack effect)
  = TE_effect TyMachine TyMachine

-- TODO: rename Machine. reference Execution Machine with X. prefix
data TyMachine = TM
  { stack :: TyStack -- currently just the type of the stack
  -- TODO: we also need the return stack
  -- TODO: and we need info relating to here/compiling
  }

-- TODO: rename Stack
data TyStack
  = TS_cons TyStack TyValue
--  | TS_empty
  | TS_var TVar
  | TS_exists String -- existential state. you dont get to pick! skolem?


-- TODO: rename Elem, as in stack elem
data TyValue -- the type of a 16-bit value, or cell. things which can be stack items
  = T_num -- 16 bit numeric value; may be a char/bool
  | T_addr TyAddr -- 16 bit address of something
--  | T_var Int -- TODO, need this

-- TODO: rename Addr (need Execution version to be reference with X. prefix)
data TyAddr -- the type of the slot at an address
  = TA_xt TyEffect -- slot containg XT with an effect
--  | TA_call TyEffect -- ( s -- s' ) slot containing call with effect
--  | TA_char -- char* -- slot containing a char
--  | TA_lit TyValue -- T* -- slot containing a 16-bit value
  -- No variable here!

----------------------------------------------------------------------
-- Show

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

----------------------------------------------------------------------
-- varsOf*

varsOfEffect :: TyEffect -> Set TVar
varsOfEffect = \case
  TE_effect m1 m2 -> varsOfMachine m1 `Set.union` varsOfMachine m2

varsOfMachine :: TyMachine -> Set TVar
varsOfMachine = \case
  TM{stack} -> varsOfStack stack

varsOfStack :: TyStack -> Set TVar
varsOfStack = \case
  TS_cons s v -> varsOfStack s `Set.union` varsOfValue v
  TS_var x -> Set.singleton x
  TS_exists{} -> Set.empty

varsOfValue :: TyValue -> Set TVar
varsOfValue = \case
  T_num -> Set.empty
  T_addr a -> varsOfAddr a

varsOfAddr :: TyAddr -> Set TVar
varsOfAddr = \case
  TA_xt e -> varsOfEffect e

----------------------------------------------------------------------
-- sub*

subEffect :: Sub -> TyEffect -> TyEffect
subEffect sub = \case
    TE_effect m1 m2 ->
      TE_effect (subMachine sub m1) (subMachine sub m2)

subMachine :: Sub -> TyMachine -> TyMachine
subMachine sub = \case
  TM{stack} -> TM { stack = subStack sub stack }

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

subValue :: Sub -> TyValue -> TyValue
subValue sub = \case
  T_num -> T_num
  T_addr a -> T_addr (subAddr sub a)

subAddr :: Sub -> TyAddr -> TyAddr
subAddr sub = \case
  TA_xt e -> TA_xt (subEffect sub e)

----------------------------------------------------------------------
-- unify*

unifyEffect :: TyEffect -> TyEffect -> Infer ()
unifyEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m1 m3
      unifyMachine m2 m4

unifyMachine :: TyMachine -> TyMachine -> Infer ()
unifyMachine m1 m2 = do
  case (m1,m2) of
    (TM{stack=s1},TM{stack=s2}) ->
      unifyStack s1 s2

unifyStack :: TyStack -> TyStack -> Infer ()
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

unifyValue :: TyValue -> TyValue -> Infer ()
unifyValue v1 v2 =
  case (v1,v2) of
    (T_num,T_num) -> pure ()
    (T_num,T_addr{}) -> Nope "num/addr"
    (T_addr{},T_num) -> Nope "addr/num"
    (T_addr a1, T_addr a2) -> unifyAddr a1 a2

unifyAddr :: TyAddr -> TyAddr -> Infer ()
unifyAddr a1 a2 =
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
  InfSubst :: TVar -> TyStack -> Infer ()
  Nope :: String -> Infer a
  CurrentSub :: Infer Sub
  Fresh :: Infer TVar


type InfRes a = IO (Either TypeError (a,Subst))

runInfer :: Infer a -> InfRes a
runInfer inf0 = loop state0 inf0 k0
  where
    k0 :: a -> State -> InfRes a
    k0 a State{subst} = pure (Right (a,subst)) -- TODO: refine here!

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
        k (useSubst subst) s
      Fresh -> do
        let State{u} = s
        let x = TVar u
        k x s { u = u + 1 }

data State = State { subst :: Subst, u :: Int }

state0 :: State
state0 = State { subst = subst0, u = 0 }

----------------------------------------------------------------------
-- Subst

data Sub = Sub (TVar -> Maybe TyStack) -- functional rep -- TODO: kill, just use subst?

useSubst :: Subst -> Sub
useSubst (Subst m) = Sub (\v -> Map.lookup v m)

applySub :: Sub -> TVar -> Maybe TyStack
applySub (Sub f) = f

data Subst = Subst (Map TVar TyStack) -- TODO: Need 2nd map for non stack vars

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

extendSubst :: Subst -> TVar -> TyStack -> Subst
extendSubst (Subst m) key replacement = do
  let g = Sub (\v -> if v==key then Just replacement else Nothing)
  let mShifted = Map.map (subStack g) m
  Subst (Map.insert key replacement mShifted)

-- TODO: need a 2nd type for vars whicah can bind to value-types
-- How name things to make it clear when have value/stack vars ?
data TVar = TVar Int -- currently only stacks can be variable
  deriving (Eq,Ord)

data TypeError = TypeError String

deriving instance Show TypeError

