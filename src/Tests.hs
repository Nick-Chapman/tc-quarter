
module Tests (run) where

import Testing (test,Testing,TestCase(..),Expect(..))

import Types
  ( makeScheme, Trans
  , (~~>), (~), num, xt, mkSVar, mkEVar, mkCVar, addr, addr_cell
  )

import qualified Testing (run)

run :: IO ()
run = Testing.run $ do

  let
    setup = unlines
      [ ":' ^^?> ^??> ;"
      , ":~ ^^?> ^??> ^>?> ;"
      , ":# 'L ~L, ~> ~, ;"
      , ":i ~L ^B?, ~>~H~@ 0# ~, ;"
      , ":t ~D~H~@~W~-~W~! ;"
      ]

  let
    -- Yes, we can infer a type
    yes :: String -> Trans -> Testing ()
    yes code trans = test TestCase { setup, code } (ExpectInfer (makeScheme trans))

  let
    -- No, we get a type error
    no :: String -> Testing ()
    no code = test TestCase { setup, code } ExpectError { frag = "" }

    nox :: String -> String -> Testing ()
    nox code frag = test TestCase { setup, code } ExpectError { frag }

    see :: String -> Testing ()
    see code = test TestCase { setup, code } ExpectError { frag = "WHAT" }

  let _ = see

  let
    s = mkSVar 101
    s1 = mkSVar 102
    x1 = mkEVar 103
    x2 = mkEVar 104
    c1 = mkCVar 105

  yes "  ~?~>" $ (s ~ num) ~~> s
  yes "~^~?~>" $ s ~~> s

  yes "~O~O" $ (s ~ x1 ~ x2) ~~> (s ~ x1 ~ x2 ~ x1 ~ x2)
  no "~D~!"

  yes "~H~@" $ s ~~> (s ~ addr c1)
  yes "~H~@~@" $ s ~~> (s ~ x1)
  yes "~H~@~C" $ s ~~> (s ~ num)

  yes "~L ^B?, ~>~H~@ 0# ~," $ s ~~> (s ~ addr c1) -- if
  yes "~D~H~@~W~-~W~! " $ (s ~ addr_cell num) ~~> s -- then

  yes "~D~@~W~!" $ (s ~ addr_cell x1) ~~> s
  nox "~D~C~W~!" $ "Num ~ Char"

  nox "i ~1    t ~1" $ "stack cyclic"
  yes "i ~1 ~, t ~1" $ (s ~ x1) ~~> (s ~ num)
  yes "i ~1 ~X t ~1" $ (s ~ x1) ~~> (s ~ num)
  nox "i ~1 ~X t"    $ "stack cyclic"
  yes "i    ~X t"    $ (s ~ x1) ~~> s

  yes "~1~X" $ s ~~> (s ~ num)

  nox "~L  1, ~V" $ "Num ~ &("
  yes "~L '1, ~V" $ s ~~> (s ~ num)
  yes "~L 'D, ~V" $ (s ~ x1) ~~> (s ~ x1 ~ x1)
  yes "~L 'P, ~V" $ (s ~ x1) ~~> s
  yes "~L  1, ~+" $ (s ~ x1) ~~> (s ~ x1)
  nox "~L '1, ~+" $ ") ~ Num"

  yes "~0~V" $ s ~~> s1
  yes "~1~+~V" $ (s ~ xt(s ~~> s1)) ~~> s1
