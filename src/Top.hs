
module Top (main) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Data.Word (Word16)
import Text.Printf (printf)


main :: IO ()
main = do
  putStrLn "*quarter-spec*"
  src <- readFile "/home/nic/code/quarter-forth/f/quarter.q"
  let src' = takeWhile (/='H') src
  go src'

go :: String -> IO ()
go s = do
  let e = kernelEffect
  let m = machine0
  let i = runEff m e
  runInteraction s i

data Interaction
  = IFinal Machine
  | ICR Interaction
  | IPut Char Interaction
  | IGet (Maybe Char -> Interaction)
  | IDebug Machine Interaction
  | IMessage String Interaction

runInteraction :: String -> Interaction -> IO ()
runInteraction = loop 0
  where
    loop :: Int -> String -> Interaction -> IO ()
    loop n inp = \case -- n counts the gets
      IFinal machine -> do
        --printf "Remaining input: '%s'" inp
        printf "\n%s\n" (seeFinalMachine machine)
        pure ()
      IDebug m i -> do
        printf " %s\n" (show m)
        loop n inp i
      IMessage mes i -> do
        printf "**%s\n" mes
        loop n inp i
      ICR i -> do
        --putStrLn "" --(show ("ICR"))
        loop n inp i
      IPut _c i -> do
        --putStr ['(',_c,')'] --(show ("IPut:",c))
        loop n inp i
      IGet f -> do
        case inp of
          [] -> loop (n+1) inp (f Nothing)
          c:inp -> do
            printf "%s" [c]
            loop (n+1) inp (f (Just c))

data Prim
  = Kdx_K | Kdx_D | Kdx_X
  | Key | Dispatch | Execute
  | Emit | CR | Nop | SetTabEntry
  | CompileComma
  | CompileRet
  | Comma
  | Zero
  | Lit | Branch0
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
  , ('B', AP Branch0)
  ]

kernelEffect :: Eff ()
kernelEffect = prim Kdx_K

prim :: Prim -> Eff ()
prim p = do
  --Message (printf "prim: %s" (show p))
  prim1 p
  a <- RsPop
  exec a

prim1 :: Prim -> Eff ()
prim1 = \case
  Kdx_K -> do
    --Debug
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
    --Debug -- good place
    v <- PsPop
    exec (addrOfValue v)
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
    a <- bump
    v <- PsPop
    UpdateMem a (SlotCall (addrOfValue v))
  Comma -> do
    v <- PsPop
    a <- bump
    UpdateMem a (SlotLit v)
  CompileRet -> do
    a <- bump
    UpdateMem a SlotRet
  Zero -> do
    PsPush (valueOfNumb 0)
  Lit -> do
    --Debug
    a <- RsPop
    slot <- LookupMem a
    case slot of
      SlotLit v -> do
        let a' = nextAddr a
        --Message (printf "Lit: %s, r: %s->%s" (show v) (show a) (show a'))
        PsPush v
        RsPush a'
        --Debug
      _ -> do
        error (printf "Lit: unexpected following slot: %s" (show slot))

  Branch0 -> do
    undefined

bump :: Eff Addr
bump = do
  a <- E_Here
  BumpHere
  pure a

exec :: Addr -> Eff ()
exec a0 = do
  x <- LookupMem a0
  --Message (printf "exec: %s --> %s" (show a0) (show x))
  case x of
    SlotPrim p -> prim p
    SlotCall a -> do
      RsPush (nextAddr a0)
      exec a
    SlotRet -> do
      a <- RsPop
      exec a
    SlotLit{} ->
      undefined
    --SlotChar{} -> undefined

instance Functor Eff where fmap = liftM
instance Applicative Eff where pure = Return; (<*>) = ap
instance Monad Eff where (>>=) = Bind

data Eff a where
  Return :: a -> Eff a
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
  LookupMem :: Addr -> Eff Slot
  UpdateMem :: Addr -> Slot -> Eff ()
  PsPush :: Value -> Eff ()
  PsPop :: Eff Value
  RsPush :: Addr -> Eff ()
  RsPop :: Eff Addr

runEff :: Machine -> Eff () -> Interaction
runEff m e = loop m e k0
  where
    k0 :: () -> Machine -> Interaction
    k0 () m = IFinal m

    loop :: Machine -> Eff a -> (a -> Machine -> Interaction) -> Interaction
    loop m e k = case e of
      Return a -> k a m
      Bind e f -> loop m e $ \a m -> loop m (f a) k
      Debug -> do IDebug m $ k () m
      Message s -> do IMessage s $ k () m
      Get -> IGet (\case Just c -> k c m; Nothing -> k0 () m)
      Put c -> IPut c $ k () m
      E_CR -> ICR $ k () m
      E_Here -> do
        let Machine{here} = m
        k (AN here) m
      BumpHere -> do
        let Machine{here} = m
        k () m { here = here + 1 }
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
  , mem :: Map Addr Slot
  , here :: Int
  }

instance Show Machine where
  show Machine{pstack=_p,rstack=_r} = do
    printf "%s ; %s" (show (reverse _p)) (show _r)
    --printf "%s" (show (reverse _p))

seeFinalMachine :: Machine -> String
seeFinalMachine m@Machine{mem} =
  unlines [ show m , dumpMem mem ]

machine0 :: Machine
machine0 = Machine
  { pstack = []
  , rstack = []
  , dispatchTable = dispatchTable0
  , mem = mem0
  , here = 0
  }

type Mem = Map Addr Slot


dumpMem :: Mem -> String
dumpMem mem = do
  unlines
    [ printf "%s : %s" (show a) (unwords (map show slots))
    | (a,slots) <- collectDef (AN 0) (AN 0) []
    ]
  where
    collectDef :: Addr -> Addr -> [Slot] -> [(Addr,[Slot])]
    collectDef a0 a acc =
      case Map.lookup a mem of
        Nothing -> [(a0,reverse acc)]
        Just slot ->
          case slot of
            SlotRet -> do
              let a' = nextAddr a
              (a0,reverse (slot:acc)) : collectDef a' a' []
            _ ->
              collectDef a0 (nextAddr a) (slot:acc)

mem0 :: Mem
mem0 = Map.fromList [ (AP p, SlotPrim p) | p <- allPrims ]
  where allPrims = [minBound..maxBound]


data Addr = AP Prim | AN Int
  deriving (Eq,Ord)

instance Show Addr where
  show = \case
    AP p -> printf "&%s" (show p)
    AN n -> printf "&%d" n

nextAddr :: Addr -> Addr
nextAddr = \case
  AN i -> AN (i+1)
  a -> error (show ("nextAddr",a))

data Slot
  = SlotPrim Prim
  | SlotCall Addr
  | SlotRet
  | SlotLit Value
  -- | SlotChar Char

instance Show Slot where
  show = \case
    SlotPrim p -> printf "*%s" (show p)
    SlotCall a -> printf "*%s" (show a)
    SlotRet -> printf "*ret"
    SlotLit v -> printf "#%s" (show v)
    -- SlotChar c -> printf "#'%s'" [c]


data Value = VC Char | VN Word16 | VA Addr

instance Show Value where
  show = \case
    VC c -> printf "'%s'" [c]
    VN n -> printf "%d" n
    VA a -> show a

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
