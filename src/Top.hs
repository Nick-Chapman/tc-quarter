
module Top (main) where

import Control.Monad (when)
import Data.List.Extra (trim)
import Execution (Interaction(..),Loc(..),Def(..))
import System.Environment (getArgs)
import System.FilePath (takeDirectory)
import System.IO (hFlush, stdout)
import Text.Printf (printf)
import TypeChecking (tc,Tenv(..),tenv0,lookupTenv)
import qualified Execution as X (interaction,State(..))
import qualified Tests (run)

main :: IO ()
main = do
  putStrLn "*tc-quarter*"
  args <- getArgs
  config <- parse config0 args
  run config

data Config = Config
  { runUnitTest :: Bool
  , listFileMaybe :: Maybe FilePath
  , reportInfer :: Bool
  , runTC :: Bool
  }

config0 :: Config
config0 =
  Config
  { runUnitTest = False
  , listFileMaybe = Nothing
  , runTC = False
  , reportInfer = False
  }

parse :: Config -> [String] -> IO Config
parse config = \case
  [] -> pure config
  "-unit":args -> parse config { runUnitTest = True } args
  "-tc":args -> parse config { runTC = True } args
  "-ti":args -> parse config { runTC = True, reportInfer = True } args
  file:args ->
    parse config { listFileMaybe = Just file } args

run :: Config -> IO ()
run config@Config{listFileMaybe,runUnitTest} =
  case listFileMaybe of
    Nothing -> Tests.run
    Just listFile -> do
      when runUnitTest $ Tests.run
      files <- readListFile listFile
      inp <- inputFiles files
      runInteraction config inp X.interaction

readListFile :: FilePath -> IO [FilePath]
readListFile path = do
  let dir = takeDirectory path
  s <- readFile path
  pure
    [ dir ++ "/" ++ filename
    | line <- lines s
    , let filename = trim (takeWhile (not . (== '#')) line)
    , filename /= ""
    ]

runInteraction :: Config -> Input -> Interaction -> IO ()
runInteraction Config{runTC,reportInfer} = loop tenv0
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
      ITC m a defs i -> if not runTC then loop tenv inp i else do
        e <- TypeChecking.tc m tenv a
        case e of
          (tenv,__subst) -> do
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
