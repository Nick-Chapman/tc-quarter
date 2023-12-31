
module Types
  ( Scheme(..), makeScheme
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Contents(..)
  , SVar(..), svarsOfStack
  , EVar(..), evarsOfElem
  , CVar(..), cvarsOfContents
  -- convenience constructors
  , (~~>), (~), xt, num, addr, addr_cell, char, mkSVar, mkEVar, mkCVar
  , unknownS, unknownE
  ) where

import Text.Printf (printf)
import Data.List (nub)

-- The polymorphic type scheme assigned to primitive and user defs
data Scheme
  = Scheme [SVar] [EVar] [CVar] Trans

makeScheme :: Trans -> Scheme
makeScheme t = Scheme
  (nub (svarsOfTrans t))
  (nub (evarsOfTrans t))
  (nub (cvarsOfTrans t))
  t

-- Type of a machine tranformation -- TODO: Consider renaming this as Type
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
  | S_Unknown -- skolem/existential. you dont get to pick!
  | S_Var SVar -- (s1,s2,...)

-- Type of a stack-element (fits in one cell)
data Elem
  = E_Number
  | E_Address Contents
  | E_Unknown
  | E_Var EVar -- (e1,e2,...)

-- Type of the contents of an address
data Contents
  = C_Char
  | C_Elem Elem
  | C_Code Trans
  | C_Var CVar -- (c1,c2,...)

data SVar = SVar Int
  deriving (Eq,Ord)

data EVar = EVar Int
  deriving (Eq,Ord)

data CVar = CVar Int
  deriving (Eq,Ord)

deriving instance Eq Trans
deriving instance Eq Machine
deriving instance Eq Stack
deriving instance Eq Elem
deriving instance Eq Contents

----------------------------------------------------------------------
-- convenience constructors

(~~>) :: Stack -> Stack -> Trans
(~~>) stack1 stack2 = T_Trans (Machine stack1) (Machine stack2)

(~) :: Stack -> Elem -> Stack
(~) stack elem = S_Cons stack elem

xt :: Trans -> Elem
xt = E_Address . C_Code

num :: Elem
num = E_Number

addr :: Contents -> Elem
addr = E_Address

addr_cell :: Elem -> Elem
addr_cell = E_Address . C_Elem

char :: Contents
char = C_Char

mkSVar :: Int -> Stack
mkSVar = S_Var . SVar

mkEVar :: Int -> Elem
mkEVar = E_Var . EVar

mkCVar :: Int -> Contents
mkCVar = C_Var . CVar

unknownS :: Stack
unknownS = S_Unknown

unknownE :: Elem
unknownE = E_Unknown

----------------------------------------------------------------------
-- Show

instance Show Scheme where
  show = \case
    Scheme svars evars cvars trans -> do
      let xs = map show svars ++ map show evars ++ map show cvars
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
    S_Unknown -> "S?"
    S_Var v -> show v

instance Show Elem where
  show = \case
    E_Number -> "Num"
    E_Address c -> printf "&%s" (show c)
    E_Unknown -> "X?"
    E_Var v -> show v

instance Show Contents where
  show = \case
    C_Char -> "Char"
    C_Elem e -> printf "%s" (show e)
    C_Code t -> show t
    C_Var v -> show v

instance Show SVar where
  show = \case
    SVar 0 -> "s" -- bit less noisy
    SVar n -> printf "s%s" (show n)

instance Show EVar where
  show (EVar n) = printf "x%s" (show n)

instance Show CVar where
  show (CVar n) = printf "c%s" (show n)

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
  S_Unknown -> []

svarsOfElem :: Elem -> [SVar]
svarsOfElem = \case
  E_Number -> []
  E_Address c -> svarsOfContents c
  E_Unknown -> []
  E_Var{} -> []

svarsOfContents :: Contents -> [SVar]
svarsOfContents = \case
  C_Char -> []
  C_Elem e -> svarsOfElem e
  C_Code t -> svarsOfTrans t
  C_Var{} -> []

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
  S_Unknown -> []

evarsOfElem :: Elem -> [EVar]
evarsOfElem = \case
  E_Number -> []
  E_Address c -> evarsOfContents c
  E_Unknown -> []
  E_Var x -> [x] -- collect here

evarsOfContents :: Contents -> [EVar]
evarsOfContents = \case
  C_Char -> []
  C_Elem e -> evarsOfElem e
  C_Code t -> evarsOfTrans t
  C_Var{} -> []

----------------------------------------------------------------------
-- cvarsOf*

cvarsOfTrans :: Trans -> [CVar]
cvarsOfTrans = \case
  T_Trans m1 m2 -> cvarsOfMachine m1 ++ cvarsOfMachine m2

cvarsOfMachine :: Machine -> [CVar]
cvarsOfMachine = \case
  Machine{stack} -> cvarsOfStack stack

cvarsOfStack :: Stack -> [CVar]
cvarsOfStack = \case
  S_Cons s e -> cvarsOfStack s ++ cvarsOfElem e
  S_Var{} -> []
  S_Unknown -> []

cvarsOfElem :: Elem -> [CVar]
cvarsOfElem = \case
  E_Number -> []
  E_Address c -> cvarsOfContents c
  E_Unknown -> []
  E_Var{} -> []

cvarsOfContents :: Contents -> [CVar]
cvarsOfContents = \case
  C_Char -> []
  C_Elem e -> cvarsOfElem e
  C_Code t -> cvarsOfTrans t
  C_Var x -> [x] -- collect here
