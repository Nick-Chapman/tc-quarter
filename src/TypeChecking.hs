
module TypeChecking
  ( tcMachine, extra
  , Scheme(..), makeScheme
  , Trans(..), Machine(..), Stack(..), Elem(..), Numeric(..), Contents(..)
  , SVar(..), EVar(..)
  , runInfer,tcStart, TypeError
  , canonicalizeScheme
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Text.Printf (printf)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (nub)

import Execution
  ( Slot(..), Addr(..)
  , Numb
  , seeChar
  , offsetAddr, slotSize
  , Prim(..)
  , Value(..)
  )

import qualified Execution as X
  ( Machine(..) -- TODO: choose different names for exection & type checking types!
  , numbOfValue
  )

extra :: String
extra = ""

tcMachine :: X.Machine -> IO ()
tcMachine m@X.Machine{dispatchTable=dt,mem} = do
  let _all = [ x | (_,x) <- Map.toList userQDefs ]
  mapM_ tcDef _all
  where
    tcDef :: Char -> IO ()
    tcDef c = do
      let _slots = slotsForDef c
      --printf "%s : %s\n" (seeChar c) (unwords (map _seeSlot _slots))
      either <- runInfer (tcStart m c)
      case either of
        Left e -> do
          printf "%s :: ERROR: %s\n" (seeChar c) (show e)
        Right ty ->
          printf "%s :: %s\n" (seeChar c) (show ty)

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
    _seeSlot :: Slot -> String
    _seeSlot = \case
      SlotCall (AN n) -> printf "*%s" (seeUserQ n)
      --SlotLit v -> printf "#%s" (seeValue v)
      slot -> show slot

    _seeValue :: Value -> String
    _seeValue = \case
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

tcStart :: X.Machine -> Char -> Infer Trans
tcStart m@X.Machine{dispatchTable=dt,mem} c = do
  case Map.lookup c dt of
    Nothing ->
      Nope (printf "no dispatch table entry for %s" (seeChar c))
    Just (AN n) -> do
      aVars <- Map.fromList <$> sequence
        [ do
            s1 <- S_Var <$> FreshS
            s2 <- S_Var <$> FreshS
            let trans = s1 ~~> s2
            pure (n,trans)
        | (_,AN n) <- Map.toList dt
        ]
      loopA aVars n
    Just{} -> do
      Nope (printf "non-user dispatch table entry for %s" (seeChar c))

 where
  loopA :: Map Numb Trans -> Numb -> Infer Trans
  loopA aVars n = do
    t1 <- loop (AN n)
    let t2 = getAddrVar n
    unifyTrans t1 t2
    pure t1

   where

    getAddrVar :: Numb -> Trans
    getAddrVar n =
       case Map.lookup n aVars of
         Nothing -> error "lookup-aVars failed"
         Just tr -> tr

    loop :: Addr -> Infer Trans
    loop a = do
      --Message (printf "loop: %s" (show a))
      (t1,as) <- tcAddr a
      --Message (printf "loop: %s: %s" (show a) (show t1))
      case as of
        [] ->
          pure t1

        [a] -> do
          t2 <- loop a
          composeTrans t1 t2

        [aX,aY] -> do
          t2 <- loop aX
          t2' <- loop aY
          unifyTrans t2 t2'
          composeTrans t1 t2
        _ ->
          undefined

    tcAddr :: Addr -> Infer (Trans, [Addr])
    tcAddr a = do
      case Map.lookup a mem of
        Nothing ->
          Nope (printf "tcAddr: nothing at address %s" (show a))
        Just slot ->
          tcSlot (offsetAddr (slotSize slot) a) slot

    tcSlot :: Addr -> Slot -> Infer (Trans,[Addr])
    tcSlot a slot = do
      let nope tag = Nope (printf "tcSlot(%s): %s" tag (show slot))
      case slot of
        SlotLit{} -> nope "lit"
        SlotChar{} -> nope "char"
        SlotEntry{} -> nope "entry"
        SlotString{} -> nope "string"
        SlotRet -> do
          t <- noTrans
          pure (t,[])
        SlotCall callAddr ->
          tcCall a callAddr

    tcCall :: Addr -> Addr -> Infer (Trans,[Addr])
    tcCall a callAddr = do
      let nope = Nope (printf "tcCall: %s" (show callAddr))
      case callAddr of
        APE{} -> nope
        AS{} -> nope
        AH{} -> nope

        AN n -> do
          -- TODO: calling sub defs -- need to maintain somekind of type env
          -- currently we just get an unbound trans of from : s1 -- s2
          let trans = getAddrVar n
          pure (trans, [a])

        AP prim ->
          tcPrim a prim

    tcPrim :: Addr -> Prim -> Infer (Trans,[Addr])
    tcPrim a = \case
      Exit -> do
        trans <- noTrans
        pure (trans,[])
      Jump -> do
        trans <- tcPrim1 Jump
        pure (trans,[])
      Branch0 -> do
        trans <- tcPrim1 Branch0
        let (a1,a2) = getBranchDests m a
        pure (trans, [a1,a2])
      Lit -> do
        let (value,a') = expectLit m a
        elem <- tcLitValue value
        stack <- S_Var <$> FreshS
        let trans = stack ~~> (stack ~ elem)
        pure (trans, [a'])
      prim -> do
        trans <- tcPrim1 prim
        pure (trans,[a])

    tcLitValue :: Value -> Infer Elem
    tcLitValue = \case
      VN{} -> pure num
      VC{} -> pure num -- needed for standard def of '('
      VA addr -> do
        litAddr addr

    litAddr :: Addr -> Infer Elem
    litAddr = \case
      AP prim -> do
        trans <- tcPrim1 prim
        pure (E_XT trans)
      AN n -> do
        pure (E_XT (getAddrVar n))
      a ->
        Nope (printf "litAddr: %s" (show a))


getBranchDests :: X.Machine -> Addr -> (Addr,Addr)
getBranchDests X.Machine{mem} a =
  case Map.lookup a mem of
    Nothing ->
      error (printf "doBranch: nothing at address %s" (show a))
    Just slot ->
      case slot of
        SlotLit v -> do
          let n = fromIntegral $ X.numbOfValue v
          (offsetAddr 2 a, offsetAddr n a)
        _ ->
          error (printf "doBranch: unexpected non-lit slot after Branch0 %s"
                 (show slot))


expectLit :: X.Machine -> Addr -> (Value,Addr)
expectLit X.Machine{mem} a =
  case Map.lookup a mem of
    Nothing ->
      error (printf "expectLit: nothing at address %s" (show a))
    Just slot ->
      case slot of
        SlotLit lit -> (lit, offsetAddr (slotSize slot) a)
        _ ->
          error (printf "expectLit: unexpected non-lit slot: %s" (show (a,slot)))



composeTrans :: Trans -> Trans -> Infer Trans
composeTrans e1 e2 = do
  case (e1,e2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      unifyMachine m2 m3
      pure (T_Trans m1 m4)

noTrans :: Infer Trans
noTrans = do
  x <- FreshS
  let s = S_Var x
  let m = Machine { stack = s }
  pure (T_Trans m m)

----------------------------------------------------------------------
-- Language of Types

data Scheme
  = Scheme [SVar] [EVar] Trans

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

deriving instance Eq Trans
deriving instance Eq Machine
deriving instance Eq Stack
deriving instance Eq Elem
deriving instance Eq Numeric
deriving instance Eq Contents

----------------------------------------------------------------------
-- Show

instance Show Scheme where
  show = \case
    Scheme svars evars trans -> do
      let xs = map show svars ++ map show evars
      printf "forall %s. %s" (unwords xs) (show trans)

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
    E_XT t -> show t -- printf "XT%s" (show e)
    E_Var v -> show v

instance Show Numeric where
  show = \case
    N_Number -> "Num"
    N_Address c -> printf "&%s" (show c)

instance Show Contents where
  show = \case
    C_Char -> "Char"
    C_Elem e -> printf "%s" (show e)

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

  Dup -> scheme $ (s1 ~ e1) ~~> (s1 ~ e1 ~ e1)

  Swap -> scheme $ (s1 ~ e1 ~ e2) ~~> (s1 ~ e2 ~ e1)

  Minus -> scheme $ (s1 ~ e1 ~ e1) ~~> (s1 ~ num) -- TODO: only allow numerics!
  --Minus -> scheme $ (s1 ~ num ~ num) ~~> (s1 ~ num) -- TODO: more general - any numerics!

  HerePointer -> scheme $ s1 ~~> (s1 ~ addr (addr e1))

  Fetch -> scheme $ (s1 ~ addr e1) ~~> (s1 ~ e1)
  C_Fetch -> scheme $ (s1 ~ addr_char) ~~> (s1 ~ num)

  Store -> scheme $ (s1 ~ e1 ~ addr e1) ~~> s1

  One -> scheme $ s1 ~~> (s1 ~ num)
  Zero -> scheme $ s1 ~~> (s1 ~ num) -- TODO: more general

  Add -> scheme $ (s1 ~ num ~ num) ~~> (s1 ~ num) -- TODO: more general - any numerics

  Branch0 -> scheme $ (s1 ~ num) ~~> s1 -- pops one elem

  Lit -> scheme $ s1 ~~> (s1 ~ e1) -- pushes one elem -- TODO: e1 should be skolem

  Jump -> scheme $ (s1 ~ xt(s1 ~~> s2)) ~~> s2

  Drop -> scheme $ s1 ~ e1 ~~> s1

  Emit -> scheme $ s1 ~ num ~~> s1

  Comma -> scheme $ s1 ~ num ~~> s1 -- overly specific
  C_Comma -> scheme $ s1 ~ num ~~> s1

  Equal -> scheme $ (s1 ~ e1 ~ e1) ~~> (s1 ~ num)
  LessThan -> scheme $ (s1 ~ e1 ~ e1) ~~> (s1 ~ num)

  IsHidden -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ num)
  IsImmediate -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ num)
  XtToNext -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ xt (s4 ~~> s5)) -- skolem!

  Execute -> scheme $ (s1 ~ xt(s1 ~~> s2)) ~~> s2

  CR -> scheme $ (s1 ~~> s1)
  CrashOnlyDuringStartup -> scheme $ (s1 ~~> s1)

  Latest -> scheme $ s1 ~~> (s1 ~ xt (S_Skolem "S1" ~~> S_Skolem "S2"))

  XtToName -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ addr_char)

  RetComma -> scheme $ (s1 ~~> s1)

  _ -> Nothing

  where
    -- TODO: move Language of types + these convenience constructors to sep file
    scheme = Just . makeScheme

    s1 = mkSVar 11
    s2 = mkSVar 22
    s3 = mkSVar 33
    s4 = mkSVar 44
    s5 = mkSVar 55

    mkSVar = S_Var . SVar

    e1 = mkEVar 111
    e2 = mkEVar 222

    mkEVar = E_Var . EVar

(~~>) :: Stack -> Stack -> Trans
(~~>) stack1 stack2 =
  T_Trans (Machine stack1) (Machine stack2)

(~) :: Stack -> Elem -> Stack
(~) stack elem = S_Cons stack elem

addr :: Elem -> Elem
addr = E_Numeric . N_Address . C_Elem

addr_char :: Elem
addr_char = E_Numeric $ N_Address C_Char

xt :: Trans -> Elem
xt = E_XT

num :: Elem
num = E_Numeric N_Number



makeScheme :: Trans -> Scheme
makeScheme t = Scheme (nub (svarsOfTrans t)) (nub (evarsOfTrans t)) t

tcPrim1 :: Prim -> Infer Trans
tcPrim1 prim =
  case schemeOfPrim prim of
    Nothing -> Nope (printf "tcPrim1: %s" (show prim))
    Just scheme -> do
      t <- instantiateScheme scheme
      --Message (printf "%s:: %s" (show prim) (show t))
      pure t

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
-- svarsOf*

svarsOfTrans :: Trans -> [SVar] -- TODO: avoid quad
svarsOfTrans = \case
  T_Trans m1 m2 -> svarsOfMachine m1 ++ svarsOfMachine m2

svarsOfMachine :: Machine -> [SVar]
svarsOfMachine = \case
  Machine{stack} -> svarsOfStack stack

svarsOfStack :: Stack -> [SVar]
svarsOfStack = \case
  S_Cons s e -> svarsOfStack s ++ svarsOfElem e
  S_Var x -> [x] -- collect here
  S_Skolem{} -> []

svarsOfElem :: Elem -> [SVar]
svarsOfElem = \case
  E_Numeric n -> svarsOfNumeric n
  E_XT t -> svarsOfTrans t
  E_Var{} -> []

svarsOfNumeric :: Numeric -> [SVar]
svarsOfNumeric = \case
  N_Number -> []
  N_Address c -> svarsOfContents c

svarsOfContents :: Contents -> [SVar]
svarsOfContents = \case
  C_Char -> []
  C_Elem e -> svarsOfElem e

----------------------------------------------------------------------
-- evarsOf*

evarsOfTrans :: Trans -> [EVar]
evarsOfTrans = \case
  T_Trans m1 m2 -> evarsOfMachine m1 ++ evarsOfMachine m2

evarsOfMachine :: Machine -> [EVar]
evarsOfMachine = \case
  Machine{stack} -> evarsOfStack stack

evarsOfStack :: Stack -> [EVar]
evarsOfStack = \case
  S_Cons s e -> evarsOfStack s ++ evarsOfElem e
  S_Var{} -> []
  S_Skolem{} -> []

evarsOfElem :: Elem -> [EVar]
evarsOfElem = \case
  E_Numeric n -> evarsOfNumeric n
  E_XT t -> evarsOfTrans t
  E_Var x -> [x] -- collect here

evarsOfNumeric :: Numeric -> [EVar]
evarsOfNumeric = \case
  N_Number -> []
  N_Address c -> evarsOfContents c

evarsOfContents :: Contents -> [EVar]
evarsOfContents = \case
  C_Char -> []
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
unifyStack s1x s2x = do
  sub <- CurrentSub
  let s1 = subStack sub s1x
  let s2 = subStack sub s2x
  let nope = Nope (printf "stack mismatch: %s ~ %s" (show s1) (show s2))
  let cyclic = Nope (printf "stack cyclic: %s ~ %s" (show s1) (show s2))
  case (subStack sub s1, subStack sub s2) of

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


unifyElem :: Elem -> Elem -> Infer ()
unifyElem e1x e2x = do
  sub <- CurrentSub
  let e1 = subElem sub e1x
  let e2 = subElem sub e2x
  let nope = Nope (printf "elem mismatch: %s ~ %s" (show e1) (show e2))
  let cyclic = Nope (printf "elem cyclic: %s ~ %s" (show e1) (show e2))
  case (e1, e2) of

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
unifyContents c1 c2 =
  case (c1,c2) of
    (C_Char,C_Char) -> pure ()
    (C_Elem e1, C_Elem e2) -> unifyElem e1 e2

    (C_Char, C_Elem{}) -> nope
    (C_Elem{}, C_Char) -> nope
  where
    nope = Nope (printf "unifyContents: %s ~ %s" (show c1) (show c2))

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

data TypeError = TypeError String

deriving instance Show TypeError
