
module PrimTyping
  ( typeOfPrim
  ) where

import Prim (Prim(..))

import Types
  ( Trans
  , (~~>), (~), xt, num, addr, addr_cell, char, mkSVar, mkEVar, mkCVar, skolem
  )

typeOfPrim :: Prim -> Trans
typeOfPrim = \case
  Add -> (s ~ x1 ~ num) ~~> (s ~ x1)
  Branch0 -> (s ~ x1) ~~> s
  CR -> (s ~~> s)
  C_Comma -> s ~ num ~~> s
  C_Fetch -> (s ~ addr char) ~~> (s ~ num)
  Comma -> s ~ x1 ~~> s
  CompileComma -> (s ~ xt (s2 ~~> s3)) ~~> s
  CrashOnlyDuringStartup -> (s ~~> s)
  --Dispatch -> (s ~ num) ~~> (s ~ xt (skolem "Sx" ~~> skolem "Sy"))
  Dispatch -> (s ~ num) ~~> (s ~ xt (s2 ~~> s3)) -- TODO: magical thinking
  Drop -> s ~ x1 ~~> s
  Dup -> (s ~ x1) ~~> (s ~ x1 ~ x1)
  Emit -> s ~ num ~~> s
  Equal -> (s ~ x1 ~ x1) ~~> (s ~ num)

  Execute -> (s ~ xt(s ~~> s2)) ~~> s2
  --Execute -> (s ~ xt(s ~~> s2)) ~~> s3 -- TODO: magic

  Fetch -> (s ~ addr_cell x1) ~~> (s ~ x1)
  HerePointer -> s ~~> (s ~ addr_cell (addr c1))
  IsHidden -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  IsImmediate -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  Jump -> (s ~ xt(s ~~> s2)) ~~> s2
  Key -> s ~~> (s ~ num)
  --Latest -> s ~~> (s ~ xt (skolem "Sx" ~~> skolem "Sy"))
  Latest -> s ~~> (s ~ xt (s2 ~~> s3))
  LessThan -> (s ~ x1 ~ x1) ~~> (s ~ num)
  Lit -> s ~~> (s ~ x1) -- TODO: x1 should be skolem
  Minus -> (s ~ x1 ~ x1) ~~> (s ~ num)
  One -> s ~~> (s ~ num)
  Over -> (s ~ x1 ~ x2) ~~> (s ~ x1 ~ x2 ~ x1)
  RetComma -> (s ~~> s)
  Store -> (s ~ x1 ~ addr_cell x1) ~~> s
  Swap -> (s ~ x1 ~ x2) ~~> (s ~ x2 ~ x1)
  XtToName -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ addr char)
  XtToNext -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ xt (s4 ~~> s5)) -- TODO: skolem!
  Zero -> s ~~> (s ~ x1) -- an XT can be zero :(

  EntryComma -> do
    (s ~ addr char) ~~> s -- TODO ??

  Kdx_K -> undefined
  Kdx_D -> undefined
  Kdx_X -> undefined
  SetTabEntry -> undefined
  Nop -> undefined

  Branch -> s ~~> s

  Exit -> undefined -- TODO here also?
  Mul -> (s ~ num ~ num) ~~> (s ~ num)
  Xor -> (s ~ num ~ num) ~~> (s ~ num)

  Crash -> s ~~> s2 -- TODO: magic, ok

  FlipImmediate ->
    (s ~ xt (s2 ~~> s3)) ~~> s

  FlipHidden ->
    (s ~ xt (s2 ~~> s3)) ~~> s

  -- TODO: Cant type return stack ops properly... (yet!)
  FromReturnStack -> s ~~> (s ~ x1)
  ToReturnStack -> (s ~ x1) ~~> s

  DivMod ->
    (s ~ num ~ num) ~~> (s ~ num ~ num)

  KeyNonBlocking -> s ~~> (s ~ num)

  C_Store -> (s ~ num ~ addr char) ~~> s

  BitShiftRight -> (s ~ num) ~~> (s ~ num)
  Sp -> s ~~> (s ~ addr_cell num)
  Sp0 -> s ~~> (s ~ addr_cell num)
  ReturnStackPointer -> s ~~> (s ~ addr_cell x1)
  ReturnStackPointerBase -> s ~~> (s ~ addr_cell x1)
  GetKey -> undefined
  Time ->  s ~~> (s ~ num ~ num)
  StartupIsComplete -> undefined
  EchoOn -> s ~~> s
  EchoEnabled -> s ~~> (s ~ num)

  where
    _x = skolem
    s = mkSVar 101
    s2 = mkSVar 102
    s3 = mkSVar 103
    s4 = mkSVar 104
    s5 = mkSVar 105
    x1 = mkEVar 106
    x2 = mkEVar 107
    c1 = mkCVar 108
