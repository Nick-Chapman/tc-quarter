
module Testing (test,run,Testing,TestCase(..),Expect(..)) where

import Control.Monad (ap,liftM)
import Data.List (isInfixOf)
import Execution (Interaction(..))
import Text.Printf (printf)
import TypeChecking (Scheme,tcStart,runInfer,canonicalizeScheme,makeScheme)
import qualified Execution as X

run :: Testing () -> IO ()
run testing = do
  bools <- sequence [ runTest i x | (i,x) <- zip [1..] (collect testing) ]
  let numTests = length bools
  let numPass = length [ () | res <- bools, res ]
  let numFail = numTests - numPass
  printf "%d tests ran; %s\n" numTests
    (if numFail > 0 then printf "%d fail." numFail else "all pass.")

test :: TestCase -> Expect -> Testing ()
test tc x = T1 (Test tc x)

instance Functor Testing where fmap = liftM
instance Applicative Testing where pure = Return; (<*>) = ap
instance Monad Testing where (>>=) = Bind

data Testing a where
  Return :: a -> Testing a
  Bind :: Testing a -> (a -> Testing b) -> Testing b
  T1 :: Test -> Testing ()

collect :: Testing () -> [Test]
collect m = loop m $ \_ -> [] where
  loop :: Testing a -> (a -> [Test]) -> [Test]
  loop m k = case m of
    Return a -> k a
    Bind m f -> loop m $ \a -> loop (f a) k
    T1 x -> x : k ()

data Test = Test TestCase Expect
data TestCase = TestCase { setup :: String, code :: String }
data Expect = ExpectError { frag :: String } | ExpectInfer Scheme

runTest :: Int -> Test -> IO Bool
runTest n (Test (TestCase{setup,code}) x) = do
  let i = X.runEff X.machine0 X.kernelEffect -- TODO: move to Execution
  mm <- runInteraction (setup++":z"++code++";") i
  case mm of
    Left err -> do
      printf "(%d) %s (execution failed)\nerr: %s\n" n code err
      pure False
    Right m -> do
      e <- runInfer (tcStart m 'z')
      case (x,e) of
        (ExpectError{frag}, Left err) -> do
          if frag `isInfixOf` (show err) then pure True else do
            printf "(%d) %s (missing frag %s in error)\ngot: %s\n" n code (show frag) (show err)
            pure False
        (ExpectInfer{}, Left err) -> do
          printf "(%d) %s (unexpected error)\ngot: %s\n" n code (show err)
          pure False
        (ExpectError{}, Right trans) -> do
          printf "(%d) %s (unexpected inference)\ngot: %s\n" n code (show trans)
          pure False
        (ExpectInfer scheme, Right trans) -> do
          let want = canonicalizeScheme scheme
          let got = canonicalizeScheme (makeScheme trans)
          if (want == got) then pure True else do
            printf "(%d) %s (infered type not as expected)\n" n code
            printf "want: %s\n" (show want)
            printf "got: %s\n" (show got)
            pure False

runInteraction :: String -> Interaction -> IO (Either String X.Machine)
runInteraction = loop
  where
    loop :: String -> Interaction -> IO (Either String X.Machine)
    loop inp = \case
      IHalt m -> do pure (Right m)
      IError s _m -> do pure (Left s)
      IDebug _m i -> do loop inp i
      IDebugMem _m i -> do loop inp i
      IMessage _mes i -> do loop inp i
      ICR i -> do loop inp i
      IPut _ i -> do loop inp i
      IGet f -> do
        case inp of
          [] -> loop inp (f Nothing)
          c:inp -> loop inp (f (Just c))
