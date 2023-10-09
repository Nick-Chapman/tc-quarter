
module Tests (run) where

import Testing (test,Testing,TestCase(..),Expect(..))

import Types
  ( makeScheme, Trans
  , (~~>), (~), num, mkSVar, mkEVar, mkNVar, addr
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
    e = mkEVar 102
    n = mkNVar 103
    e1 = mkEVar 104
    e2 = mkEVar 105
    s1 = mkSVar 106

  yes "  ~?~>" $ (s ~ num) ~~> s
  yes "~^~?~>" $ s ~~> s

  yes "~O~O" $ (s ~ e1 ~ e2) ~~> (s ~ e1 ~ e2 ~ e1 ~ e2)
  no "~D~!"

  yes "~H~@" $ s ~~> (s ~ addr e1)
  yes "~H~@~@" $ s ~~> (s ~ e1)
  --yes "~H~@~C" $ s ~~> (s ~ num) -- TODO: should pass -- need content vars

  yes "~L ^B?, ~>~H~@ 0# ~," $ s ~~> (s ~ addr e1) -- if: TODO: tighter, numeric
  yes "~D~H~@~W~-~W~! " $ (s ~ addr num) ~~> s -- then

  yes "~D~@~W~!" $ (s ~ addr e1) ~~> s
  nox "~D~C~W~!" $ "Num ~ Char"

  nox "i ~1    t ~1" $ "stack cyclic"
  yes "i ~1 ~, t ~1" $ (s ~ e) ~~> (s ~ n)
  yes "i ~1 ~X t ~1" $ (s ~ e) ~~> (s ~ n)
  nox "i ~1 ~X t"    $ "stack cyclic"
  yes "i    ~X t"    $ (s ~ e) ~~> s

  yes "~1~X" $ s ~~> (s ~ n)

  nox "~L  1, ~V" $ "Num ~ ("
  yes "~L '1, ~V" $ s ~~> (s ~ n)
  yes "~L 'D, ~V" $ (s ~ e) ~~> (s ~ e ~ e)
  yes "~L 'P, ~V" $ (s ~ e) ~~> s
  yes "~L  1, ~+" $ (s ~ n) ~~> (s ~ n)
  nox "~L '1, ~+" $ ") ~ Num"

  yes "~0~V" $ s ~~> s1 -- sadly we allow 0 as an execution token
  no "~1~+~V" -- but not the result of addition
