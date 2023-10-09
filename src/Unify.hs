
module Unify
  ( unifyTrans
  , unifyMachine
  )
  where

import Text.Printf (printf)

import Types
  ( Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Numeric(..)
  , Contents(..)
  , svarsOfStack
  , evarsOfElem
  )

import Infer
  ( Infer(..)
  , subStack, subElem
  )

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
    (S_Skolem x1, S_Skolem x2) ->
      -- TODO: can we regard a skolem as not even the same as itself?
      if (x1 == x2) then pure () else nope


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
