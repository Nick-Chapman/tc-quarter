
module Types
  ( Scheme(..), makeScheme
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Numeric(..)
  , Contents(..)
  , SVar(..), svarsOfTrans, svarsOfStack
  , EVar(..), evarsOfTrans, evarsOfElem
  -- convenience constructors
  , (~~>), (~), xt, num, addr, addr_char, mkSVar, mkEVar -- TODO: loose "mk" prefix?
  , skolem
  ) where

import Text.Printf (printf)
import Data.List (nub)

-- The polymorphic type scheme assigned to primitive and user defs
data Scheme
  = Scheme [SVar] [EVar] Trans

makeScheme :: Trans -> Scheme
makeScheme t = Scheme (nub (svarsOfTrans t)) (nub (evarsOfTrans t)) t

-- Type of a machine tranformation
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

-- Type of an element that can be treated like a number
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
-- convenience constructors

(~~>) :: Stack -> Stack -> Trans
(~~>) stack1 stack2 = T_Trans (Machine stack1) (Machine stack2)

(~) :: Stack -> Elem -> Stack
(~) stack elem = S_Cons stack elem

xt :: Trans -> Elem
xt = E_XT

num :: Elem
num = E_Numeric N_Number

addr :: Elem -> Elem
addr = E_Numeric . N_Address . C_Elem

addr_char :: Elem
addr_char = E_Numeric $ N_Address C_Char

mkSVar :: Int -> Stack
mkSVar = S_Var . SVar

mkEVar :: Int -> Elem
mkEVar = E_Var . EVar

skolem :: String ->  Stack
skolem = S_Skolem

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
    S_Skolem x -> x -- TODO: just need one, S?
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
  show (SVar n) = printf "s%s" (show n) -- TODO: specal case 0

instance Show EVar where
  show (EVar n) = printf "e%s" (show n)

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
