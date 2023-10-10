
module PrimTyping
  ( typeOfPrim
  ) where

import Prim (Prim(..))

import Types
  ( Trans
  , (~~>), (~), xt, num, addr, addr_char, mkSVar, mkEVar, skolem
  )

typeOfPrim :: Prim -> Trans
typeOfPrim = \case
  Add -> (s ~ x1 ~ num) ~~> (s ~ x1)
  Branch0 -> (s ~ x1) ~~> s
  CR -> (s ~~> s)
  C_Comma -> s ~ num ~~> s
  C_Fetch -> (s ~ addr_char) ~~> (s ~ num)
  Comma -> s ~ x1 ~~> s
  CompileComma -> (s ~ xt (s2 ~~> s3)) ~~> s
  CrashOnlyDuringStartup -> (s ~~> s)
  Dispatch -> (s ~ num) ~~> (s ~ xt (skolem "Sx" ~~> skolem "Sy"))
  Drop -> s ~ x1 ~~> s
  Dup -> (s ~ x1) ~~> (s ~ x1 ~ x1)
  Emit -> s ~ num ~~> s
  Equal -> (s ~ x1 ~ x1) ~~> (s ~ num)
  Execute -> (s ~ xt(s ~~> s2)) ~~> s2
  Fetch -> (s ~ addr x1) ~~> (s ~ x1)
  HerePointer -> s ~~> (s ~ addr (addr x1)) -- TODO: c1
  IsHidden -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  IsImmediate -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  Jump -> (s ~ xt(s ~~> s2)) ~~> s2
  Key -> s ~~> (s ~ num)
  Latest -> s ~~> (s ~ xt (skolem "Sx" ~~> skolem "Sy"))
  LessThan -> (s ~ x1 ~ x1) ~~> (s ~ num)
  Lit -> s ~~> (s ~ x1) -- TODO: x1 should be skolem
  Minus -> (s ~ x1 ~ x1) ~~> (s ~ num)
  One -> s ~~> (s ~ num)
  Over -> (s ~ x1 ~ x2) ~~> (s ~ x1 ~ x2 ~ x1)
  RetComma -> (s ~~> s)
  Store -> (s ~ x1 ~ addr x1) ~~> s
  Swap -> (s ~ x1 ~ x2) ~~> (s ~ x2 ~ x1)
  XtToName -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ addr_char)
  XtToNext -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ xt (s4 ~~> s5)) -- TODO: skolem!
  Zero -> s ~~> (s ~ x1) -- an XT can be zero :(

  Kdx_K -> undefined
  Kdx_D -> undefined
  Kdx_X -> undefined
  SetTabEntry -> undefined
  Nop -> undefined
  Branch -> undefined
  Exit -> undefined
  Mul -> undefined
  Xor -> undefined
  EntryComma  -> undefined
  Crash  -> undefined
  FlipImmediate -> undefined
  FlipHidden -> undefined
  FromReturnStack -> undefined
  ToReturnStack -> undefined
  DivMod -> undefined
  KeyNonBlocking -> undefined
  C_Store -> undefined
  BitShiftRight -> undefined
  Sp -> undefined
  Sp0 -> undefined
  ReturnStackPointer -> undefined
  ReturnStackPointerBase -> undefined
  GetKey -> undefined
  Time -> undefined
  StartupIsComplete -> undefined
  EchoOn -> undefined

  where
    s = mkSVar 101
    s2 = mkSVar 102
    s3 = mkSVar 103
    s4 = mkSVar 104
    s5 = mkSVar 105
    x1 = mkEVar 106
    x2 = mkEVar 107
