
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

      either <- runInfer (tcStart slots)
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


----------------------------------------------------------------------
-- tc entry point -- TODO: should be at level of address

tcStart :: [Slot] -> Infer Trans
tcStart = tcSlotsExec

tcSlotsExec :: [Slot] -> Infer Trans
tcSlotsExec = \case
  [] -> noTrans
  slot1:slots -> do
    e1 <- tcSlotExec slot1
    e2 <- tcSlotsExec slots
    sub <- CurrentSub
    let e1' = subTrans sub e1
    let e2' = subTrans sub e2
    composeTrans e1' e2'

noTrans :: Infer Trans
noTrans = do
  x <- Fresh
  let s = S_Var x
  let m = Machine { stack = s }
  pure (T_Trans m m)

composeTrans :: Trans -> Trans -> Infer Trans
composeTrans e1 e2 = do
  case (e1,e2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      unifyMachine m2 m3
      pure (T_Trans m1 m4)

tcSlotExec :: Slot -> Infer Trans
tcSlotExec slot = case slot of
  SlotCall a -> tcAddrExec a
  SlotRet -> noTrans
  SlotLit{} -> nope
  SlotChar{} -> nope
  SlotEntry{} -> nope
  SlotString{} -> nope
  where
    nope = Nope (printf "tcSlotExec: %s" (show slot))

tcAddrExec :: Addr -> Infer Trans
tcAddrExec a = case a of
  AP p -> tcPrimExec p
  AN{} -> nope
  APE{} -> nope
  AS{} -> nope
  AH -> nope
  where
    nope = Nope (printf "tcAddrExec: %s" (show a))

----------------------------------------------------------------------
-- Language of Types

data Scheme
  = Scheme (Set SVar) Trans

-- Type of a machine tranformation -- what occurs during execution
data Trans
  = T_Trans Machine Machine

-- Type of a machine state
data Machine = Machine
  { stack :: Stack
  -- TODO: we also need the return stack
  -- TODO: and we need info relating to here/compiling
  }

-- Type of a stack of elements
data Stack
  = S_Cons Stack Elem
--  | TS_empty
  | S_Skolem String -- existential state. you dont get to pick!
  | S_Var SVar -- (s1,s2,...)

-- Type of a stack-element (fits in a cell)
data Elem
  = E_XT Trans
  | E_Numeric Numeric
--  | E_var Int -- TODO, need this (e1,e2,...)
-- Type of a stack of elements

-- Type of thing that can b treated like a number
data Numeric
  = N_Number
  | N_Address Contents
--  | TA_var Int -- (n1,n2,...)

-- Type of the contents of an address
data Contents
  = C_Char
  | C_Elem Elem
--  | C_Var Int -- (c1,c2...)

data SVar = SVar Int -- currently only stacks can be variable
  deriving (Eq,Ord)

----------------------------------------------------------------------
-- Show

instance Show Trans where -- TODO: rename Trans -> Trans (so can use T; keep E for Elem)
  show = \case
    T_Trans m1 m2 ->
      printf "(%s -- %s)" (show m1) (show m2)

instance Show Machine where
  show = \case
    Machine{stack} -> show stack

instance Show Stack where
  show = \case
    S_Cons s v -> printf "%s %s" (show s) (show v)
    S_Var n -> show n
    S_Skolem x -> x

instance Show Elem where
  show = \case
    E_Numeric a -> show a
    E_XT e -> show e -- printf "XT%s" (show e)

instance Show Numeric where
  show = \case
    N_Number -> "Num"
    N_Address c -> printf "&%s" (show c)

instance Show Contents where
  show = \case
    C_Char -> "Char"
    C_Elem e -> printf "(%s)" (show e)

instance Show SVar where
  show (SVar n) = printf "s%s" (show n)

----------------------------------------------------------------------
-- Primitives

schemeOfPrim :: Prim -> Maybe Scheme
schemeOfPrim = \case

  Key -> scheme $ s1 ~~> (s1 ~ num)

  Dispatch -> scheme $ (s1 ~ num) ~~> (s1 ~ xt (S_Skolem "S1" ~~> S_Skolem "S2"))

  CompileComma -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> s1

  Over -> scheme $ (s1 ~ x1 ~ x2) ~~> (s1 ~ x1 ~ x2 ~ x1)
    where
      x1 = num -- Should be polymorphic. -- need polymorphic elem types
      x2 = num

  _ -> Nothing

  where
    scheme = Just . makeScheme

    (~~>) stack1 stack2 =
      T_Trans (Machine stack1) (Machine stack2)

    (~) stack elem = S_Cons stack elem

    xt = E_XT
    num = E_Numeric N_Number

    s1 = mkVar 1
    s2 = mkVar 2
    s3 = mkVar 3

    mkVar = S_Var . SVar


makeScheme :: Trans -> Scheme
makeScheme t = Scheme (varsOfTrans t) t

tcPrimExec :: Prim -> Infer Trans
tcPrimExec prim =
  case schemeOfPrim prim of
    Nothing -> Nope (printf "tcPrimExec: %s" (show prim))
    Just scheme -> instantiateScheme scheme

instantiateScheme :: Scheme -> Infer Trans
instantiateScheme (Scheme vars ty) = do
  bs <- sequence [ do y <- Fresh; pure (x,S_Var y) | x <- Set.toList vars]
  let sub = Subst (Map.fromList bs)
  pure (subTrans sub ty)

----------------------------------------------------------------------
-- varsOf*

varsOfTrans :: Trans -> Set SVar
varsOfTrans = \case
  T_Trans m1 m2 -> varsOfMachine m1 `Set.union` varsOfMachine m2

varsOfMachine :: Machine -> Set SVar
varsOfMachine = \case
  Machine{stack} -> varsOfStack stack

varsOfStack :: Stack -> Set SVar
varsOfStack = \case
  S_Cons s e -> varsOfStack s `Set.union` varsOfElem e
  S_Var x -> Set.singleton x
  S_Skolem{} -> Set.empty

varsOfElem :: Elem -> Set SVar -- TODO rename suffic Elem -> Elem
varsOfElem = \case
  E_Numeric n -> varsOfNumeric n
  E_XT t -> varsOfTrans t

varsOfNumeric :: Numeric -> Set SVar
varsOfNumeric = \case
  N_Number -> Set.empty
  N_Address c -> varsOfContents c

varsOfContents :: Contents -> Set SVar
varsOfContents = \case
  C_Char -> Set.empty
  C_Elem e -> varsOfElem e

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
        case applySubst sub var of
          Nothing -> stack
          Just replacement -> replacement
      stack@S_Skolem{} ->
        stack

subElem :: Subst -> Elem -> Elem
subElem sub = \case
  E_Numeric n -> E_Numeric (subNumeric sub n)
  E_XT t -> E_XT (subTrans sub t)

subNumeric :: Subst -> Numeric -> Numeric
subNumeric sub = \case
  N_Number -> N_Number
  N_Address c -> N_Address (subContents sub c)

subContents :: Subst -> Contents -> Contents
subContents sub = \case
  C_Char -> C_Char
  C_Elem e -> C_Elem (subElem sub e)

----------------------------------------------------------------------
-- unify*

unifyTrans :: Trans -> Trans -> Infer ()
unifyTrans t1 t2 = do
  case (t1,t2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      unifyMachine m1 m3
      unifyMachine m2 m4

unifyMachine :: Machine -> Machine -> Infer ()
unifyMachine m1 m2 = do
  case (m1,m2) of
    (Machine{stack=s1},Machine{stack=s2}) ->
      unifyStack s1 s2

unifyStack :: Stack -> Stack -> Infer ()
unifyStack s1 s2 =
  case (s1,s2) of

    (S_Var x1, stack@(S_Var x2)) ->
      if x1==x2 then pure () else InfSubst x1 stack

    (S_Var x, stack) ->
      if x `elem` varsOfStack stack then cyclic else InfSubst x stack

    (stack, S_Var x) ->
      if x `elem` varsOfStack stack then cyclic else InfSubst x stack

    (S_Cons s1 e1, S_Cons s2 e2) -> do
      unifyStack s1 s2
      unifyElem e1 e2

    (S_Cons{}, _) -> nope
    (_, S_Cons{}) -> nope
    (S_Skolem x1, S_Skolem x2) -> if (x1 == x2) then pure () else nope

  where
    nope = Nope (printf "unifyStack: %s ~ %s" (show s1) (show s2))
    cyclic = Nope (printf "cyclic: %s =!= %s" (show s1) (show s2))

unifyElem :: Elem -> Elem -> Infer ()
unifyElem e1 e2 =
  case (e1,e2) of
    (E_Numeric n1, E_Numeric n2) -> unifyNumeric n1 n2
    (E_XT t1, E_XT t2) -> unifyTrans t1 t2

    (E_Numeric{},E_XT{}) -> nope
    (E_XT{},E_Numeric{}) -> nope
  where
    nope = Nope (printf "unifyElem: %s ~ %s" (show e1) (show e2))

unifyNumeric :: Numeric -> Numeric -> Infer ()
unifyNumeric a1 a2 =
  case (a1,a2) of
    (N_Number, N_Number) -> pure ()
    (N_Address c1, N_Address c2) -> unifyContents c1 c2

    (N_Number, N_Address{}) -> nope
    (N_Address{}, N_Number) -> nope
  where
    nope = Nope (printf "unifyNumeric: %s ~ %s" (show a1) (show a2))

unifyContents :: Contents -> Contents -> Infer ()
unifyContents = undefined -- TODO!


----------------------------------------------------------------------
-- Infer

instance Functor Infer where fmap = liftM
instance Applicative Infer where pure = InfReturn; (<*>) = ap
instance Monad Infer where (>>=) = InfBind

data Infer a where
  InfReturn :: a -> Infer a
  InfBind :: Infer a -> (a -> Infer b) -> Infer b
  InfSubst :: SVar -> Stack -> Infer ()
  Nope :: String -> Infer a
  CurrentSub :: Infer Subst
  Fresh :: Infer SVar


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
        let x = SVar u
        k x s { u = u + 1 }

data State = State { subst :: Subst, u :: Int }

state0 :: State
state0 = State { subst = subst0, u = 0 }

----------------------------------------------------------------------
-- Subst

data Subst = Subst (Map SVar Stack) -- TODO: Need 2nd map for non stack vars

applySubst :: Subst -> SVar -> Maybe Stack
applySubst (Subst m) x = Map.lookup x m

domain :: Subst -> Set SVar
domain (Subst m) = Set.fromList $ Map.keys m

range :: Subst -> Set SVar
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

extendSubst :: Subst -> SVar -> Stack -> Subst
extendSubst (Subst m) key replacement = do

  let g = Subst (Map.singleton key replacement)
  let mShifted = Map.map (subStack g) m
  Subst (Map.insert key replacement mShifted)

-- TODO: need a 2nd type for vars which can bind to value-types
-- How name things to make it clear when have value/stack vars ?

data TypeError = TypeError String

deriving instance Show TypeError

