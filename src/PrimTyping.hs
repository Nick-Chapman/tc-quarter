
module PrimTyping
  ( typeOfPrim
  ) where

import Prim (Prim(..))

import Types
  ( Trans
  , (~~>), (~), xt, num, addr, addr_cell, char, mkSVar, mkEVar, mkCVar, unknownS
  )

typeOfPrim :: Prim -> Trans
typeOfPrim = \case
  -- TODO: Cant yet type return stack ops correctly
  FromReturnStack -> s ~~> (s ~ x1)
  ToReturnStack -> (s ~ x1) ~~> s
  Add -> (s ~ x1 ~ num) ~~> (s ~ x1)
  Branch0 -> (s ~ x1) ~~> s
  CR -> (s ~~> s)
  C_Comma -> s ~ num ~~> s
  C_Fetch -> (s ~ addr char) ~~> (s ~ num)
  Comma -> s ~ x1 ~~> s
  CompileComma -> (s ~ xt (s2 ~~> s3)) ~~> s
  CrashOnlyDuringStartup -> (s ~~> s)
  Dispatch -> (s ~ num) ~~> (s ~ xt (unknownS ~~> unknownS))
  Drop -> s ~ x1 ~~> s
  Dup -> (s ~ x1) ~~> (s ~ x1 ~ x1)
  Emit -> s ~ num ~~> s
  Equal -> (s ~ x1 ~ x1) ~~> (s ~ num)
  Execute -> (s ~ xt(s ~~> s2)) ~~> s2
  Fetch -> (s ~ addr_cell x1) ~~> (s ~ x1)
  HerePointer -> s ~~> (s ~ addr_cell (addr c1))
  IsHidden -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  IsImmediate -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ num)
  Jump -> (s ~ xt(s ~~> s2)) ~~> s2
  Key -> s ~~> (s ~ num)
  Latest -> s ~~> (s ~ xt (unknownS ~~> unknownS))
  LessThan -> (s ~ x1 ~ x1) ~~> (s ~ num)
  Lit -> s ~~> (s ~ x1) -- TODO: x1 should be skolem
  Minus -> (s ~ x1 ~ x1) ~~> (s ~ num)
  One -> s ~~> (s ~ num)
  Over -> (s ~ x1 ~ x2) ~~> (s ~ x1 ~ x2 ~ x1)
  RetComma -> (s ~~> s)
  Store -> (s ~ x1 ~ addr_cell x1) ~~> s
  Swap -> (s ~ x1 ~ x2) ~~> (s ~ x2 ~ x1)
  XtToName -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ addr char)
  XtToNext -> (s ~ xt (s2 ~~> s3)) ~~> (s ~ xt (unknownS ~~> unknownS))
  Zero -> s ~~> (s ~ x1)
  EntryComma -> do (s ~ addr char) ~~> s -- TODO: addr entry
  Branch -> s ~~> s
  Mul -> (s ~ num ~ num) ~~> (s ~ num)
  Xor -> (s ~ num ~ num) ~~> (s ~ num)
  Crash -> s ~~> s
  FlipImmediate -> (s ~ xt (s2 ~~> s3)) ~~> s
  FlipHidden -> (s ~ xt (s2 ~~> s3)) ~~> s
  DivMod -> (s ~ num ~ num) ~~> (s ~ num ~ num)
  KeyNonBlocking -> s ~~> (s ~ num)
  C_Store -> (s ~ num ~ addr char) ~~> s
  BitShiftRight -> (s ~ num) ~~> (s ~ num)
  Sp -> s ~~> (s ~ addr_cell num)
  Sp0 -> s ~~> (s ~ addr_cell num)
  AsNum -> (s ~ x1) ~~> (s ~ num)
  ReturnStackPointer -> s ~~> (s ~ addr_cell x1)
  ReturnStackPointerBase -> s ~~> (s ~ addr_cell x1)
  Time ->  s ~~> (s ~ num ~ num)
  EchoOn -> s ~~> s
  EchoOff -> s ~~> s
  EchoEnabled -> s ~~> (s ~ num)
  SetCursorShape -> (s ~ num) ~~> s
  SetCursorPosition -> (s ~ num) ~~> s
  ReadCharCol -> s ~~> (s ~ num ~ num)
  WriteCharCol -> (s ~ num ~ num) ~~> s
  Cls -> s ~~> s
  KEY -> s ~~> (s ~ num)
  Exit -> s ~~> s

  -- TODO: unimplemented
  Kdx_K -> undefined
  Kdx_D -> undefined
  Kdx_X -> undefined
  SetTabEntry -> undefined
  Nop -> undefined
  GetKey -> undefined
  StartupIsComplete -> undefined
  SetKey -> undefined

  where

    -- It doesn't matter what these numbers are, so long asthey are all different
    s = mkSVar 101
    s2 = mkSVar 102
    s3 = mkSVar 103
    x1 = mkEVar 106
    x2 = mkEVar 107
    c1 = mkCVar 108
