
module PrimTyping
  ( schemeOfPrim
  ) where

import Prim (Prim(..))

import Types
  ( Scheme, makeScheme
  , (~~>), (~), xt, num, addr, addr_char, mkSVar, mkEVar, skolem
  )

schemeOfPrim :: Prim -> Maybe Scheme
schemeOfPrim = \case

  Key -> scheme $ s1 ~~> (s1 ~ num)

  Dispatch -> scheme $ (s1 ~ num) ~~> (s1 ~ xt (skolem "S1" ~~> skolem "S2"))

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

  --Add -> scheme $ (s1 ~ num ~ num) ~~> (s1 ~ num) -- TODO: more general - any numerics
  Add -> scheme $ (s1 ~ e1 ~ num) ~~> (s1 ~ e1) -- TODO: too general - TC's 'q'

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

  Latest -> scheme $ s1 ~~> (s1 ~ xt (skolem "S1" ~~> skolem "S2"))

  XtToName -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ addr_char)

  RetComma -> scheme $ (s1 ~~> s1)

  _ -> Nothing

  where
    scheme = Just . makeScheme

    s1 = mkSVar 11
    s2 = mkSVar 22
    s3 = mkSVar 33
    s4 = mkSVar 44
    s5 = mkSVar 55

    e1 = mkEVar 111
    e2 = mkEVar 222
