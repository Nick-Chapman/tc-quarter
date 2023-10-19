
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
  , Contents(..)
  , svarsOfStack
  , evarsOfElem
  , cvarsOfContents
  )

import Infer
  ( Infer(..)
  , subStack, subElem, subContents
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
    (S_Unknown, S_Unknown) -> nope


unifyElem :: Elem -> Elem -> Infer ()
unifyElem e1x e2x = do
  sub <- CurrentSub
  let e1 = subElem sub e1x
  let e2 = subElem sub e2x
  let nope = Nope (printf "elem: %s ~ %s" (show e1) (show e2))
  let cyclic = Nope (printf "elem cyclic: %s ~ %s" (show e1) (show e2))
  case (e1, e2) of

    (E_Var x1, el@(E_Var x2)) ->
      if x1==x2 then pure () else SubElem x1 el

    (E_Var x, el) ->
      if x `elem` evarsOfElem el then cyclic else SubElem x el

    (el, E_Var x) ->
      if x `elem` evarsOfElem el then cyclic else SubElem x el

    (E_Number, E_Number) -> pure ()
    (E_Address c1, E_Address c2) -> unifyContents c1 c2
    (E_Unknown, E_Unknown) -> nope

    (E_Number{}, _) -> nope
    (_, E_Number{}) -> nope

    (E_Address{}, _) -> nope
    (_, E_Address{}) -> nope


unifyContents :: Contents -> Contents -> Infer ()
unifyContents c1x c2x = do
  sub <- CurrentSub
  let c1 = subContents sub c1x
  let c2 = subContents sub c2x
  let nope = Nope (printf "contents: %s ~ %s" (show c1) (show c2))
  let cyclic = Nope (printf "contents cyclic: %s ~ %s" (show c1) (show c2))
  case (c1,c2) of

    (C_Var x1, c@(C_Var x2)) ->
      if x1==x2 then pure () else SubContents x1 c

    (C_Var x, c) ->
      if x `elem` cvarsOfContents c then cyclic else SubContents x c

    (c, C_Var x) ->
      if x `elem` cvarsOfContents c then cyclic else SubContents x c

    (C_Char,C_Char) -> pure ()
    (C_Elem e1, C_Elem e2) -> unifyElem e1 e2
    (C_Code t1, C_Code t2) -> unifyTrans t1 t2

    (C_Char{}, _) -> nope
    (_, C_Char{}) -> nope
    (C_Elem{}, _) -> nope
    (_, C_Elem{}) -> nope
