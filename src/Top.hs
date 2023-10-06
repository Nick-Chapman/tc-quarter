
module Top (main) where

import Text.Printf (printf)
import System.IO (hFlush, stdout)
import Control.Monad (when)

import Execution
  ( kernelEffect
  , Machine(..), machine0
  , Interaction(..), runEff
  )

import TypeChecking (extra,tcMachine)

main :: IO ()
main = do
  putStrLn "*tc-quarter*"
  xs <- sequence
    [ readFile ("../quarter-forth/f/" ++ f)
    | f <-
        [ "quarter.q"
        -- , "forth.f"
        -- , "tools.f"
        -- , "regression.f"
        -- , "examples.f"
        -- , "primes.f"
        -- , "start.f"
        ]
    ]
  go (concat (extra:xs))

go :: String -> IO ()
go s = do
  let e = kernelEffect
  let m = machine0
  let i = runEff m e
  runInteraction s i

runInteraction :: String -> Interaction -> IO ()
runInteraction = loop 0
  where
    loop :: Int -> String -> Interaction -> IO ()
    loop n inp = \case -- n counts the gets
      IHalt _m@Machine{tick} -> do
        when (inp/="") $ printf "Remaining input: '%s'\n" inp
        printf "#machine-ticks=%d\n" tick
        tcMachine _m
      IError s _m -> do
        printf "\n**Error: %s\n" s
        --tcMachine _m
      IDebug m i -> do
        printf "%s\n" (show m)
        loop n inp i
      IDebugMem m i -> do
        tcMachine m
        loop n inp i
      IMessage mes i -> do
        printf "**%s\n" mes
        loop n inp i
      ICR i -> do
        putStrLn ""
        loop n inp i
      IPut c i -> do
        putStr [c]; flush
        loop n inp i
      IGet f -> do
        case inp of
          [] -> loop (n+1) inp (f Nothing)
          c:inp -> do
            --putStr [c] -- echo-on
            loop (n+1) inp (f (Just c))

    flush = hFlush stdout
