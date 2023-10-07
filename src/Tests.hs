
module Tests (run) where

import Testing (test,Testing,TestCase(..),Expect(..))
import TypeChecking (Elem(..),Trans(..),makeScheme,Stack(..),Machine(..),SVar(..),EVar(..))
import qualified Testing (run)

run :: IO ()
run = Testing.run $ do

  let
    setup = ":~ ^^?> ^??> ^>?> ;"

  let
    -- Yes, we can infer a type
    yes :: String -> Trans -> Testing ()
    yes code trans = test TestCase { setup, code } (ExpectInfer (makeScheme trans))

  let
    -- No, we get a type error
    no :: String -> Testing ()
    no code = test TestCase { setup, code } ExpectError { frag = "" }


  yes "~O~O" $ (s1 ~ e1 ~ e2) ~~> (s1 ~ e1 ~ e2 ~ e1 ~ e2)
  no "~D~!"

  -- no "~O~O" -- unepected inference
  -- yes "~D~!" typeForOverOver -- unexpected error
  -- yes "~O" typeForOverOver -- wrong type inferred

  where

    (~~>) stack1 stack2 =
      T_Trans (Machine stack1) (Machine stack2)

    (~) stack elem = S_Cons stack elem

    s1 = mkSVar 11

    mkSVar = S_Var . SVar

    e1 = mkEVar 44
    e2 = mkEVar 55

    mkEVar = E_Var . EVar
