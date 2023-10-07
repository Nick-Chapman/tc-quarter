
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
  mapM_ tcDef "'~23"
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
  x <- FreshS
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
  = Scheme (Set SVar) (Set EVar) Trans

-- Type of a machine tranformation -- what occurs during execution
data Trans
  = T_Trans Machine Machine

-- Type of a machine state
data Machine = Machine
  { stack :: Stack
  -- TODO: we also need the return stack
  -- TODO: and we need info relating to here/compiling
  }

-- Type of a stack (of elements)
data Stack
  = S_Cons Stack Elem
--  | TS_empty
  | S_Skolem String -- existential state. you dont get to pick!
  | S_Var SVar -- (s1,s2,...)

-- Type of a stack-element (fits in one cell)
data Elem
  = E_XT Trans
  | E_Numeric Numeric
  | E_Var EVar -- (e1,e2,...)

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

data SVar = SVar Int
  deriving (Eq,Ord)

data EVar = EVar Int
  deriving (Eq,Ord)

----------------------------------------------------------------------
-- Show

instance Show Trans where
  show = \case
    T_Trans m1 m2 ->
      printf "(%s -- %s)" (show m1) (show m2)

instance Show Machine where
  show = \case
    Machine{stack} -> show stack

instance Show Stack where
  show = \case
    S_Cons s v -> printf "%s.%s" (show s) (show v)
    S_Skolem x -> x
    S_Var v -> show v

instance Show Elem where
  show = \case
    E_Numeric a -> show a
    E_XT e -> show e -- printf "XT%s" (show e)
    E_Var v -> show v

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

instance Show EVar where
  show (EVar n) = printf "e%s" (show n)

----------------------------------------------------------------------
-- Primitives

schemeOfPrim :: Prim -> Maybe Scheme
schemeOfPrim = \case

  Key -> scheme $ s1 ~~> (s1 ~ num)

  Dispatch -> scheme $ (s1 ~ num) ~~> (s1 ~ xt (S_Skolem "S1" ~~> S_Skolem "S2"))

  CompileComma -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> s1

  Over -> scheme $ (s1 ~ e1 ~ e2) ~~> (s1 ~ e1 ~ e2 ~ e1)

  _ -> Nothing

  where
    scheme = Just . makeScheme

    (~~>) stack1 stack2 =
      T_Trans (Machine stack1) (Machine stack2)

    (~) stack elem = S_Cons stack elem

    xt = E_XT
    num = E_Numeric N_Number

    s1 = mkSVar 11
    s2 = mkSVar 22
    s3 = mkSVar 33

    mkSVar = S_Var . SVar

    e1 = mkEVar 44
    e2 = mkEVar 55

    mkEVar = E_Var . EVar


makeScheme :: Trans -> Scheme
makeScheme t = Scheme (svarsOfTrans t) (evarsOfTrans t) t

tcPrimExec :: Prim -> Infer Trans
tcPrimExec prim =
  case schemeOfPrim prim of
    Nothing -> Nope (printf "tcPrimExec: %s" (show prim))
    Just scheme -> do
      t <- instantiateScheme scheme
      --Message (printf "%s:: %s" (show prim) (show t))
      pure t

instantiateScheme :: Scheme -> Infer Trans
instantiateScheme (Scheme svars evars ty) = do
  s <- Map.fromList <$> sequence [ do y <- FreshS; pure (x,S_Var y)
                                 | x <- Set.toList svars ]
  e <- Map.fromList <$> sequence [ do y <- FreshE; pure (x,E_Var y)
                                 | x <- Set.toList evars ]
  let sub = Subst { s , e }
  pure (subTrans sub ty)

----------------------------------------------------------------------
-- svarsOf*

svarsOfTrans :: Trans -> Set SVar
svarsOfTrans = \case
  T_Trans m1 m2 -> svarsOfMachine m1 `Set.union` svarsOfMachine m2

svarsOfMachine :: Machine -> Set SVar
svarsOfMachine = \case
  Machine{stack} -> svarsOfStack stack

svarsOfStack :: Stack -> Set SVar
svarsOfStack = \case
  S_Cons s e -> svarsOfStack s `Set.union` svarsOfElem e
  S_Var x -> Set.singleton x -- collect here
  S_Skolem{} -> Set.empty

svarsOfElem :: Elem -> Set SVar
svarsOfElem = \case
  E_Numeric n -> svarsOfNumeric n
  E_XT t -> svarsOfTrans t
  E_Var{} -> Set.empty

svarsOfNumeric :: Numeric -> Set SVar
svarsOfNumeric = \case
  N_Number -> Set.empty
  N_Address c -> svarsOfContents c

svarsOfContents :: Contents -> Set SVar
svarsOfContents = \case
  C_Char -> Set.empty
  C_Elem e -> svarsOfElem e

----------------------------------------------------------------------
-- evarsOf*

evarsOfTrans :: Trans -> Set EVar
evarsOfTrans = \case
  T_Trans m1 m2 -> evarsOfMachine m1 `Set.union` evarsOfMachine m2

evarsOfMachine :: Machine -> Set EVar
evarsOfMachine = \case
  Machine{stack} -> evarsOfStack stack

evarsOfStack :: Stack -> Set EVar
evarsOfStack = \case
  S_Cons s e -> evarsOfStack s `Set.union` evarsOfElem e
  S_Var{} -> Set.empty
  S_Skolem{} -> Set.empty

evarsOfElem :: Elem -> Set EVar
evarsOfElem = \case
  E_Numeric n -> evarsOfNumeric n
  E_XT t -> evarsOfTrans t
  E_Var x -> Set.singleton x -- collect here

evarsOfNumeric :: Numeric -> Set EVar
evarsOfNumeric = \case
  N_Number -> Set.empty
  N_Address c -> evarsOfContents c

evarsOfContents :: Contents -> Set EVar
evarsOfContents = \case
  C_Char -> Set.empty
  C_Elem e -> evarsOfElem e

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
      if x1==x2 then pure () else SubStack x1 stack

    (S_Var x, stack) ->
      if x `elem` svarsOfStack stack then cyclic else SubStack x stack

    (stack, S_Var x) ->
      if x `elem` svarsOfStack stack then cyclic else SubStack x stack

    (S_Cons s1 e1, S_Cons s2 e2) -> do
      unifyStack s1 s2
      unifyElem e1 e2

    (S_Cons{}, _) -> nope
    (_, S_Cons{}) -> nope
    (S_Skolem x1, S_Skolem x2) -> if (x1 == x2) then pure () else nope

  where
    nope = Nope (printf "unifyStack: %s ~ %s" (show s1) (show s2))
    cyclic = Nope (printf "cyclic: %s ~ %s" (show s1) (show s2))

unifyElem :: Elem -> Elem -> Infer ()
unifyElem e1 e2 =
  case (e1,e2) of

    (E_Var x1, el@(E_Var x2)) ->
      if x1==x2 then pure () else SubElem x1 el

    (E_Var x, el) ->
      if x `elem` evarsOfElem el then cyclic else SubElem x el

    (el, E_Var x) ->
      if x `elem` evarsOfElem el then cyclic else SubElem x el

    (E_Numeric n1, E_Numeric n2) -> unifyNumeric n1 n2
    (E_XT t1, E_XT t2) -> unifyTrans t1 t2

    (E_Numeric{},E_XT{}) -> nope
    (E_XT{},E_Numeric{}) -> nope
  where
    nope = Nope (printf "unifyElem: %s ~ %s" (show e1) (show e2))
    cyclic = Nope (printf "cyclic: %s ~ %s" (show e1) (show e2))

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
        printf "runInfer: %s\n" mes
        k () s
      SubStack v stack -> do
        --printf "SubStack: %s -> %s\n" (show v) (show stack)
        let State{subst} = s
        let subst' = extendSubstStack subst v stack
        --printf "subst: %s\n" (show subst')
        checkInvariant subst'
        k () s { subst = subst' }
      SubElem v elem -> do
        --printf "SubElem: %s -> %s\n" (show v) (show elem)
        let State{subst} = s
        let subst' = extendSubstElem subst v elem
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
-- Subst

data Subst = Subst
  { s :: Map SVar Stack
  , e :: Map EVar Elem
  }

applySubstS :: Subst -> SVar -> Maybe Stack
applySubstS Subst {s} x = Map.lookup x s

applySubstE :: Subst -> EVar -> Maybe Elem
applySubstE Subst {e} x = Map.lookup x e

domain :: Subst -> Set SVar
domain Subst{s} = Set.fromList $ Map.keys s

range :: Subst -> Set SVar
range Subst{s} = Set.unions [ svarsOfStack v | v <- Map.elems s ]

checkInvariant :: Subst -> IO () -- TODO: invariant for all kinds of vars
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
  show Subst{s,e} =
    unwords $
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList s ] ++
    [ printf "%s: %s," (show k) (show v) | (k,v) <- Map.toList e ]

subst0 :: Subst
subst0 = Subst { s = Map.empty, e = Map.empty }

extendSubstStack :: Subst -> SVar -> Stack -> Subst
extendSubstStack Subst {s, e} key replacement = do
  let sub = Subst { s = Map.singleton key replacement, e = Map.empty }
  Subst { s = Map.insert key replacement (Map.map (subStack sub) s)
        , e = Map.map (subElem sub) e }

extendSubstElem :: Subst -> EVar -> Elem -> Subst
extendSubstElem Subst {s, e} key replacement = do
  let sub = Subst { e = Map.singleton key replacement, s = Map.empty }
  Subst { s = Map.map (subStack sub) s
        , e = Map.insert key replacement (Map.map (subElem sub) e) }

data TypeError = TypeError String

deriving instance Show TypeError
