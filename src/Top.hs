
module Top (main) where

import Execution (Interaction(..),Loc(..))
import System.IO (hFlush, stdout)
import Tests (run)
import Text.Printf (printf)
import TypeChecking (tcMachine)
import qualified Execution as X (interaction,State(..))

main :: IO ()
main = do
  Tests.run
  _main

_main :: IO ()
_main = do
  putStrLn "*tc-quarter*"
  inp <- inputFiles
    [ "../quarter-forth/f/" ++ f
    | f <-
        [ "quarter.q"
        , "forth.f"
        ]
    ]
  go inp

go :: Input -> IO ()
go s = runInteraction s X.interaction

runInteraction :: Input -> Interaction -> IO ()
runInteraction = loop
  where
    loop :: Input -> Interaction -> IO ()
    loop inp = \case
      IHalt _m@X.State{tick} -> do
        printf "#machine-ticks=%d\n" tick
        --tcMachine _m
      IError s _m -> do
        printf "\n**Error: %s\n" s
      IDebug m i -> do
        printf "%s\n" (show m)
        loop inp i
      IDebugMem m i -> do
        tcMachine m
        loop inp i
      IMessage mes i -> do
        printf "**%s\n" mes
        loop inp i
      ICR i -> do
        putStrLn ""
        loop inp i
      IPut c i -> do
        putStr [c]; flush
        loop inp i
      IGet f -> do
        (m,inp') <- nextChar inp
        loop inp' (f m)
      IWhere f -> do
        loop inp (f (location inp))

    flush = hFlush stdout

data Input = Input
  { file :: FilePath
  , row :: Int
  , col :: Int
  , str :: String
  , more :: [FilePath]
  }

inputFiles :: [FilePath] -> IO Input
inputFiles = \case
  [] -> error "inputFiles[]"
  file:more -> do
    --printf "**Reading file: %s\n" file
    str <- readFile file
    pure Input { file, row = 1, col = 0, str, more }

nextChar :: Input -> IO (Maybe Char,Input)
nextChar i@Input{str,row,col,more} =
  case str of
    x:xs -> if
      | x =='\n' -> pure (Just x, i { str = xs, row = row + 1, col = 0 })
      | otherwise -> pure (Just x, i { str = xs, col = col + 1 })
    [] ->
      case more of
        [] -> pure (Nothing, i)
        file:more -> do
          --printf "**Reading file: %s\n" file
          str <- readFile file
          nextChar $ Input { file, row = 1, col = 0, str, more }

location :: Input -> Loc
location Input{file,row,col} = Loc {file,row,col}
