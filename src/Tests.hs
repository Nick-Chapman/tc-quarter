
module Tests (run) where

import Testing (test,Testing,TestCase(..),Expect(..))

import Types
  ( makeScheme, Trans, Stack, Contents, Machine
  , (~), num, xt, mkSVar, mkEVar, mkCVar, addr, addr_cell, cell_addr, contents
  , mkTrans, mkMachine, char
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
      , ":h ~H~@ ;"
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


  let
    h = mkCVar 100
    s = mkSVar 101
    s1 = mkSVar 102
    x1 = mkEVar 103
    x2 = mkEVar 104
    c1 = mkCVar 105
    --c2 = mkCVar 106

  let
    (~~>) :: Stack -> Stack -> Trans
    (~~>) stack1 stack2 = do
      mkTrans (mkMachine h stack1) (mkMachine h stack2)

    (~~~>) :: Machine -> Machine -> Trans
    (~~~>) = mkTrans

    (/) :: Contents -> Stack -> Machine
    (/) = mkMachine

  let _ = (see,no,nox,yes,s1,x1,x2,num,xt,addr_cell,s,c1,(~~>),(~),addr
          , (~~~>),(/),cell_addr
          )

  yes "  ~?~>" $ (s ~ num) ~~> s
  yes "~^~?~>" $ s ~~> s

  yes "~O~O" $ (s ~ x1 ~ x2) ~~> (s ~ x1 ~ x2 ~ x1 ~ x2)
  no "~D~!"

  yes "~H~@" $ s ~~> (s ~ addr h)
  yes "~H~@~@" $ (contents x1/s) ~~~> (contents x1 / (s ~ x1))
  yes "~H~@~C" $ (char/s) ~~~> (char/ (s ~ num))

  yes "~L ^B?, ~>~H~@ 0# ~," $ s ~~> (s ~ addr h) -- if
  yes "~D~H~@~W~-~W~! " $ (contents num/(s ~ addr_cell num)) ~~~> (contents num/s) -- then

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

  yes "~H~@" $ s ~~> (s ~ addr h)
  yes "~H~@ ~H~@" $ s ~~> (s ~ addr h ~ addr h)

  -- TODO: typecheck setup code so "h" works the same as "H@"
  -- yes "~h" $ s ~~> (s ~ addr c1)
  -- yes "~h ~h" $ s ~~> (s ~ addr c1 ~ addr c1)
