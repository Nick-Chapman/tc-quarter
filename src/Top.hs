
module Top (main) where

import Control.Monad (when)
import Execution (Interaction(..),Loc(..),Def(..))
import System.IO (hFlush, stdout)
import Tests (run)
import Text.Printf (printf)
import TypeChecking (tc,Tenv(..),tenv0,lookupTenv)
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
        -- TODO: read this from ../quarter-forth/full.list
        [ "quarter.q"
        , "forth.f"
        , "tools.f"
        , "regression.f"
        , "examples.f"
        , "primes.f"
        , "snake.f"
        , "buffer.f"
        , "start.f"
        ]
    ]
  go inp

go :: Input -> IO ()
go s = runInteraction s X.interaction

runInteraction :: Input -> Interaction -> IO ()
runInteraction = loop tenv0
  where
    loop :: Tenv -> Input -> Interaction -> IO ()
    loop tenv inp = \case
      IHalt _m@X.State{tick} -> do
        printf "#machine-ticks=%d\n" tick
        let Tenv{nErrs} = tenv
        printf "#errors=%d\n" nErrs
      IError s _m -> do
        printf "\n**Error: %s\n" s
        print _m
      IDebug m i -> do
        printf "%s\n" (show m)
        loop tenv inp i
      IDebugMem _m i -> do
        loop tenv inp i
      IMessage mes i -> do
        printf "**%s\n" mes
        loop tenv inp i
      ICR i -> do
        putStrLn ""
        loop tenv inp i
      IPut c i -> do
        putStr [c]; flush
        loop tenv inp i
      IGet f -> do
        (m,inp') <- nextChar inp
        loop tenv inp' (f m)
      IWhere f -> do
        loop tenv inp (f (location inp))
      ITC m a defs i -> do
        e <- TypeChecking.tc m tenv a
        case e of
          (tenv,__subst) -> do
            let
              reportInfer = True
            when reportInfer $
              sequence_ [ report tenv def | def <- defs ]
            loop tenv inp i

    flush = hFlush stdout

report :: Tenv -> Def -> IO ()
report tenv = \case
  Def_Dispatch c a -> do
    let ts = lookupTenv a tenv
    printf "?%c :: %s\n" c (show ts)
  Def_Dictionary name a -> do
    let ts = lookupTenv a tenv
    printf "%s :: %s\n" name (show ts)


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
