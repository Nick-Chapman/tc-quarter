
module Top (main) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Data.Word (Word16)

main :: IO ()
main = do
  putStrLn "*quarter-spec*"
  src <- readFile "/home/nic/code/quarter-forth/f/quarter.q"
  go src

go :: String -> IO ()
go s = do
  let e = kernelEffect
  let m = machine0
  let i = runEff m e
  runInteraction s i

data Interaction
  = IHalt
  | ICR Interaction
  | IPut Char Interaction
  | IGet (Char -> Interaction)
  | IDebug Machine Interaction
  | IMessage String Interaction

runInteraction :: String -> Interaction -> IO ()
runInteraction = loop
  where
    loop :: String -> Interaction -> IO ()
    loop inp = \case
      IHalt -> do
        putStrLn (show ("IHalt: remaining string:",inp))
        pure ()
      IDebug m i -> do
        putStrLn (show ("IDebug:",m))
        loop inp i
      IMessage s i -> do
        putStrLn (show ("IMessage:",s))
        loop inp i
      ICR i -> do
        putStrLn "" --(show ("ICR"))
        loop inp i
      IPut c i -> do
        putStr ['(',c,')'] --(show ("IPut:",c))
        loop inp i
      IGet f -> do
        case inp of
          [] -> putStrLn (show ("string run out"))
          c:inp -> do
            putStr [c] -- (show ("IGet:",c))
            runInteraction inp (f c)

data Prim
  = Kdx_K | Kdx_D | Kdx_X
  | Key | Dispatch | Execute
  | Emit | CR | Nop | SetTabEntry
  | CompileComma
  | CompileRet
  | Comma
  | Zero
  | Lit
  deriving (Eq,Ord,Show,Enum,Bounded)

dispatchTable0 :: Map Char Addr
dispatchTable0 = Map.fromList
  [ ('^', AP Key)
  , ('?', AP Dispatch)
  , ('.', AP Emit)
  , ('M', AP CR)
  , ('\n', AP Nop)
  , (' ', AP Nop)
  , (':', AP SetTabEntry)
  , ('>', AP CompileComma)
  , (',', AP Comma)
  , (';', AP CompileRet)
  , ('0', AP Zero)
  , ('L', AP Lit)
  ]

kernelEffect :: Eff ()
kernelEffect = prim Kdx_K

prim :: Prim -> Eff ()
prim p = do
  prim1 p
  a <- RsPop
  runAddress a

prim1 :: Prim -> Eff ()
prim1 = \case
  Kdx_K -> do
    RsPush (AP Kdx_D)
    prim Key
  Kdx_D -> do
    RsPush (AP Kdx_X)
    prim Dispatch
  Kdx_X -> do
    RsPush (AP Kdx_K)
    prim Execute
  Key -> do
    c <- Get
    PsPush (valueOfChar c)
  Dispatch -> do
    v <- PsPop
    a <- LookupDT (charOfValue v)
    PsPush (valueOfAddr a)
  Execute -> do
    v <- PsPop
    runAddress (addrOfValue v)
  Emit -> do
    v <- PsPop
    Put (charOfValue v)
  CR -> do
    E_CR
  Nop -> do
    pure ()
  SetTabEntry -> do
    c <- Get
    a <- E_Here
    UpdateDT c a
  CompileComma -> do
    (a,a') <- bump
    v <- PsPop
    UpdateMem a (CCall (addrOfValue v) a')
  Comma -> do
    v <- PsPop
    (a,_) <- bump
    UpdateMem a (CValue v)
  CompileRet -> do
    (a,_) <- bump
    UpdateMem a CRet
  Zero -> do
    PsPush (valueOfNumb 0)
  Lit -> do
    undefined

bump :: Eff (Addr,Addr)
bump = do
  a <- E_Here
  BumpHere
  a' <- E_Here
  pure (a,a')

runCode :: Contents -> Eff ()
runCode = \case
  CPrim p -> prim p
  CCall xt a -> do
    RsPush a
    runAddress xt
  CRet -> do
    a <- RsPop
    runAddress a
  CValue{} ->
    undefined
  CChar{} ->
    undefined

runAddress :: Addr -> Eff ()
runAddress a = do
  x <- LookupMem a
  runCode x

instance Functor Eff where fmap = liftM
instance Applicative Eff where pure = Ret; (<*>) = ap
instance Monad Eff where (>>=) = Bind

data Eff a where
  Ret :: a -> Eff a
  Bind :: Eff a -> (a -> Eff b) -> Eff b
  Debug :: Eff ()
  Message :: String -> Eff ()
  Get :: Eff Char
  Put :: Char -> Eff ()
  E_CR :: Eff ()
  E_Here :: Eff Addr
  BumpHere :: Eff ()
  LookupDT :: Char -> Eff Addr
  UpdateDT :: Char -> Addr -> Eff ()
  LookupMem :: Addr -> Eff Contents
  UpdateMem :: Addr -> Contents -> Eff ()
  PsPush :: Value -> Eff ()
  PsPop :: Eff Value
  RsPush :: Addr -> Eff ()
  RsPop :: Eff Addr

runEff :: Machine -> Eff () -> Interaction
runEff m e = loop m e k0
  where
    k0 :: () -> Machine -> Interaction
    k0 () _ = IHalt

    loop :: Machine -> Eff a -> (a -> Machine -> Interaction) -> Interaction
    loop m e k = case e of
      Ret a -> k a m
      Bind e f -> loop m e $ \a m -> loop m (f a) k
      Debug -> do IDebug m $ k () m
      Message s -> do IMessage s $ k () m
      Get -> IGet (\c -> k c m)
      Put c -> IPut c $ k () m
      E_CR -> ICR $ k () m
      E_Here -> do
        let Machine{here} = m
        k here m
      BumpHere -> do
        let Machine{here} = m
        k () m { here = nextAddr here }
      LookupDT c -> do
        let Machine{dispatchTable=dt} = m
        let a = maybe err id $ Map.lookup c dt
              where err = error (show ("lookupDT",c))
        k a m
      UpdateDT c a -> do
        let Machine{dispatchTable=dt} = m
        k () m { dispatchTable = Map.insert c a dt }
      LookupMem a -> do
        let Machine{mem} = m
        let x = maybe err id $ Map.lookup a mem
              where err = error (show ("lookupMem",a))
        k x m
      UpdateMem a x -> do
        let Machine{mem} = m
        k () m { mem = Map.insert a x mem }
      PsPush v -> do
        let Machine{pstack} = m
        k () m { pstack = v:pstack }
      PsPop -> do
        let Machine{pstack} = m
        case pstack of
          [] -> error "PsPop[]"
          v:pstack -> k v m { pstack }
      RsPush a -> do
        let Machine{rstack} = m
        k () m { rstack = a:rstack }
      RsPop -> do
        let Machine{rstack} = m
        case rstack of
          [] -> error "RsPop[]"
          v:rstack -> k v m { rstack }

data Machine = Machine
  { pstack :: [Value]
  , rstack :: [Addr]
  , dispatchTable :: Map Char Addr
  , mem :: Map Addr Contents
  , here :: Addr
  }
  deriving Show

machine0 :: Machine
machine0 = Machine
  { pstack = []
  , rstack = []
  , dispatchTable = dispatchTable0
  , mem = mem0
  , here = AN 0
  }

mem0 :: Map Addr Contents
mem0 = Map.fromList [ (AP p, CPrim p) | p <- allPrims ]
  where allPrims = [minBound..maxBound]

data Addr = AP Prim | AN Int
  deriving (Eq,Ord,Show)

nextAddr :: Addr -> Addr
nextAddr = \case
  AN i -> AN (i+1)
  a -> error (show ("nextAddr",a))

data Contents
  = CPrim Prim
  | CCall Addr Addr
  | CRet
  | CValue Value
  | CChar Char
  deriving Show

data Value = VC Char | VN Word16 | VA Addr deriving Show

valueOfChar :: Char -> Value
valueOfChar = VC

charOfValue :: Value -> Char
charOfValue = \case VC c -> c ; v -> error (show ("charOfValue",v))

valueOfAddr :: Addr -> Value
valueOfAddr = VA

addrOfValue :: Value -> Addr
addrOfValue = \case VA a -> a ; v -> error (show ("addrOfValue",v))

valueOfNumb :: Numb -> Value
valueOfNumb = VN

--numbOfValue :: Value -> Numb
--numbOfValue = \case VN a -> a ; v -> error (show ("numbOfValue",v))

type Numb = Word16
