
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
  Add -> (s ~ e1 ~ num) ~~> (s ~ e1) -- TODO: only allow numerics
  Branch0 -> (s ~ num) ~~> s
  CR -> (s ~~> s)
  C_Comma -> s ~ num ~~> s
  C_Fetch -> (s ~ addr_char) ~~> (s ~ num)
  Comma -> s ~ num ~~> s -- TODO: overly specific; allow only numerics
  CompileComma -> (s ~ xt (s2 ~~> s3)) ~~> s
  CrashOnlyDuringStartup -> (s ~~> s)
  Dispatch -> (s ~ num) ~~> (s ~ xt (skolem "Sx" ~~> skolem "Sy"))
  Drop -> s ~ e1 ~~> s
  Dup -> (s ~ e1) ~~> (s ~ e1 ~ e1)
  Emit -> s ~ num ~~> s
  Equal -> (s ~ e1 ~ e1) ~~> (s ~ num)
  Execute -> (s ~ xt(s ~~> s2)) ~~> s2
  Fetch -> (s ~ addr e1) ~~> (s ~ e1)
  HerePointer -> s ~~> (s ~ addr (addr e1))
  IsHidden -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  IsImmediate -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  Jump -> (s ~ xt(s ~~> s2)) ~~> s2
  Key -> s ~~> (s ~ num)
  Latest -> s ~~> (s ~ xt (skolem "Sx" ~~> skolem "Sy"))
  LessThan -> (s ~ e1 ~ e1) ~~> (s ~ num)
  Lit -> s ~~> (s ~ e1) -- TODO: e1 should be skolem
  Minus -> (s ~ e1 ~ e1) ~~> (s ~ num) -- TODO: only allow numerics!
  One -> s ~~> (s ~ num)
  Over -> (s ~ e1 ~ e2) ~~> (s ~ e1 ~ e2 ~ e1)
  RetComma -> (s ~~> s)
  Store -> (s ~ e1 ~ addr e1) ~~> s
  Swap -> (s ~ e1 ~ e2) ~~> (s ~ e2 ~ e1)
  XtToName -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ addr_char)
  XtToNext -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ xt (s4 ~~> s5)) -- TODO: skolem!
  Zero -> s ~~> (s ~ num) -- TODO: more general

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
    e1 = mkEVar 106
    e2 = mkEVar 107
