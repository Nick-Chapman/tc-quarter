
module Top (main) where

import Control.Monad (when)
import System.IO (hFlush, stdout)
import Tests (run)
import Text.Printf (printf)
import TypeChecking (extra,tcMachine)

import Execution (Interaction(..))
import qualified Execution as X (interaction,State(..))

main :: IO ()
main = do
  Tests.run
  _main

_main :: IO ()
_main = do
  putStrLn "*tc-quarter*"
  xs <- sequence
    [ readFile ("../quarter-forth/f/" ++ f)
    | f <-
        [ "quarter.q"
        , "forth.f"
        , "tools.f"
        --, "regression.f"
        , "examples.f"
        --, "primes.f"
        , "start.f"
        ]
    ]
  go (concat (extra:xs++["umm\nz cr\n"]))

go :: String -> IO ()
go s = runInteraction s X.interaction

runInteraction :: String -> Interaction -> IO ()
runInteraction = loop 0
  where
    loop :: Int -> String -> Interaction -> IO ()
    loop n inp = \case -- n counts the gets
      IHalt m@X.State{tick} -> do
        when (inp/="") $ printf "Remaining input: '%s'\n" inp
        printf "#machine-ticks=%d\n" tick
        tcMachine m
      IError s _m -> do
        printf "\n**Error: %s\n" s
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
