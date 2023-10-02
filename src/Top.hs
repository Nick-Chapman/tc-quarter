
module Top (main) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Data.Word (Word16)
import Text.Printf (printf)
import Data.Char as Char (chr,ord)

main :: IO ()
main = do
  putStrLn "*quarter-spec*"
  --src <- readFile "/home/nic/code/quarter-forth/f/quarter.q"
  src <- readFile "q+f"
  go src

go :: String -> IO ()
go s = do
  let e = kernelEffect
  let m = machine0
  let i = runEff m e
  runInteraction s i

data Interaction
  = IHalt
  | IError String Machine
  | ICR Interaction
  | IPut Char Interaction
  | IGet (Maybe Char -> Interaction)
  | IDebug Machine Interaction
  | IDebugMem Machine Interaction
  | IMessage String Interaction

runInteraction :: String -> Interaction -> IO ()
runInteraction = loop 0
  where
    loop :: Int -> String -> Interaction -> IO ()
    loop n inp = \case -- n counts the gets
      IHalt -> do
        --printf "Remaining input: '%s'" inp
        pure ()
      IError s _m -> do
        printf "\n**Error: %s" s
        --printf "\n%s\n" (seeFinalMachine _m)
        pure ()
      IDebug m i -> do
        printf " %s\n" (show m)
        loop n inp i
      IDebugMem m i -> do
        printf "\n%s\n" (seeFinalMachine m)
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
            printf "%c" c
            loop (n+1) inp (f (Just c))

data Prim
  = Kdx_K | Kdx_D | Kdx_X -- TODO: meh
  | Key | Dispatch | SetTabEntry
  | Execute | Exit | Jump
  | Emit | CR | Nop
  | HerePointer
  | CompileComma | CompileRet | Comma | C_Comma
  | Lit | Branch0
  | Fetch | Store
  | C_Fetch
  | Dup | Swap | Over | Drop
  | Zero | One | Minus | Add | Mul | Equal | LessThan
  | EntryComma | XtNext | XtName | Latest | IsHidden | IsImmediate
  | CrashOnlyDuringStartup
  deriving (Eq,Ord,Show,Enum,Bounded)

kernelEffect :: Eff ()
kernelEffect = prim Kdx_K

prim :: Prim -> Eff ()
prim p = do
  --Debug
  --Message (printf "prim: %s" (show p))
  prim1 p
  a <- RsPop
  exec a

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
  SetTabEntry -> do
    c <- Get
    a <- E_Here
    UpdateDT c a
  Execute -> do
    v <- PsPop
    exec (addrOfValue v)
  Exit -> do
    _ <- RsPop
    pure ()
  Jump -> do
    _ <- RsPop
    v <- PsPop
    RsPush (addrOfValue v)
  Emit -> do
    v <- PsPop
    Put (charOfValue v)
  CR -> do
    E_CR
  Nop -> do
    pure ()
  HerePointer -> do
    a <- E_HereAddr
    PsPush (valueOfAddr a)
  CompileComma -> do
    a <- bump
    v <- PsPop
    UpdateMem a (SlotCall (addrOfValue v))
  CompileRet -> do
    a <- bump
    UpdateMem a SlotRet
  Comma -> do
    v <- PsPop
    a <- bump
    UpdateMem a (SlotLit v)
  C_Comma -> do
    v <- PsPop
    a <- bump
    UpdateMem a (SlotChar (charOfValue v))
  Lit -> do
    a <- RsPop
    slot <- LookupMem a
    let v = valueOfSlot slot
    let a' = nextAddr a
    PsPush v
    RsPush a'
  Branch0 -> do
    a <- RsPop
    slot <- LookupMem a
    v <- PsPop
    let a' = if isZero v then offsetAddr a (valueOfSlot slot) else nextAddr a
    RsPush a'
  Fetch -> do
    v1 <- PsPop
    slot <- LookupMem (addrOfValue v1)
    PsPush (valueOfSlot slot)
  C_Fetch -> do
    v1 <- PsPop
    slot <- LookupMem (addrOfValue v1)
    PsPush (valueOfChar (charOfSlot slot))
  Store -> do
    vLoc <- PsPop
    v <- PsPop
    UpdateMem (addrOfValue vLoc) (SlotLit v)
  Dup -> do
    v <- PsPop
    PsPush v
    PsPush v
  Swap -> do
    v1 <- PsPop
    v2 <- PsPop
    PsPush v1
    PsPush v2
  Over -> do
    v1 <- PsPop
    v2 <- PsPop
    PsPush v2
    PsPush v1
    PsPush v2
  Drop -> do
    _ <- PsPop
    pure ()
  Zero -> do
    PsPush (valueOfNumb 0)
  One -> do
    PsPush (valueOfNumb 1)
  Minus -> do
    v2 <- PsPop
    v1 <- PsPop
    PsPush (valueMinus v1 v2)
  Add -> do
    v2 <- PsPop
    v1 <- PsPop
    PsPush (valueAdd v1 v2)
  Mul -> do
    v2 <- PsPop
    v1 <- PsPop
    PsPush (valueMul v1 v2)
  Equal -> do
    v2 <- PsPop
    v1 <- PsPop
    PsPush (valueEqual v1 v2)
  LessThan -> do
    v2 <- PsPop
    v1 <- PsPop
    PsPush (valueLessThan v1 v2)
  EntryComma -> do
    pure () -- TODO
  XtNext -> do
    undefined
  XtName -> do
    undefined
  Latest -> do
    undefined
  IsHidden -> do
    undefined
  IsImmediate -> do
    undefined
  CrashOnlyDuringStartup -> do
    undefined

bump :: Eff Addr -- TODO: prim effect?
bump = do
  a <- E_Here
  BumpHere
  pure a

exec :: Addr -> Eff ()
exec a0 = do
  LookupMem a0 >>= \case
    SlotPrim p -> prim p
    SlotCall a -> do
      RsPush (nextAddr a0)
      exec a
    SlotRet -> do
      a <- RsPop
      exec a
    SlotLit{} ->
      error "exec: SLotLit"
    SlotChar{} ->
      error "exec: SlotChar"

instance Functor Eff where fmap = liftM
instance Applicative Eff where pure = Return; (<*>) = ap
instance Monad Eff where (>>=) = Bind

data Eff a where
  Return :: a -> Eff a
  Bind :: Eff a -> (a -> Eff b) -> Eff b
  Debug :: Eff ()
  DebugMem :: Eff ()
  Message :: String -> Eff ()
  E_Abort :: Eff ()
  Get :: Eff Char
  Put :: Char -> Eff ()
  E_CR :: Eff ()
  LookupDT :: Char -> Eff Addr
  UpdateDT :: Char -> Addr -> Eff ()
  LookupMem :: Addr -> Eff Slot
  UpdateMem :: Addr -> Slot -> Eff ()
  PsPush :: Value -> Eff ()
  PsPop :: Eff Value
  RsPush :: Addr -> Eff ()
  RsPop :: Eff Addr
  E_HereAddr :: Eff Addr
  E_Here :: Eff Addr
  BumpHere :: Eff ()

runEff :: Machine -> Eff () -> Interaction
runEff m e = loop m e k0
  where
    k0 :: () -> Machine -> Interaction
    k0 () _m = do
      --IDebugMem _m $
        IHalt

    loop :: Machine -> Eff a -> (a -> Machine -> Interaction) -> Interaction
    loop m e k = case e of
      Return a -> k a m
      Bind e f -> loop m e $ \a m -> loop m (f a) k
      Debug -> do IDebug m $ k () m
      DebugMem -> do IDebugMem m $ k () m
      Message s -> do IMessage s $ k () m
      E_Abort -> IError "Abort" m
      Get -> IGet (\case Just c -> k c m; Nothing -> k0 () m)
      Put c -> IPut c $ k () m
      E_CR -> ICR $ k () m
      LookupDT c -> do
        let Machine{dispatchTable=dt} = m
        case Map.lookup c dt of
          Nothing -> IError (show ("lookupDT",c)) m
          Just a -> k a m
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
      E_HereAddr -> do
        let Machine{hereAddr=a} = m
        k a m
      E_Here -> do
        let Machine{hereAddr=a,mem} = m
        let err = error "E_Here"
        let slot = maybe err id $ Map.lookup a mem
        k (addrOfValue (valueOfSlot slot)) m
      BumpHere -> do
        let Machine{hereAddr=a,mem} = m
        let err = error "BumpHere"
        let slot = maybe err id $ Map.lookup a mem
        let slot' = SlotLit (valueOfAddr (nextAddr (addrOfValue (valueOfSlot slot))))
        k () m { mem = Map.insert a slot' mem }

data Machine = Machine
  { pstack :: [Value]
  , rstack :: [Addr]
  , dispatchTable :: Map Char Addr
  , mem :: Map Addr Slot
  , hereAddr :: Addr
  }

instance Show Machine where
  show Machine{pstack=_p,rstack=_r} = do
    printf "%s ; %s" (show (reverse _p)) (show _r)

seeFinalMachine :: Machine -> String
seeFinalMachine m@Machine{mem} =
  unlines [ show m , dumpMem mem ]

machine0 :: Machine
machine0 = Machine
  { pstack = []
  , rstack = []
  , dispatchTable = dispatchTable0
  , mem = mem0
  , hereAddr = AN 0
  }

dispatchTable0 :: Map Char Addr
dispatchTable0 = Map.fromList
  [ ('\n',AP Nop)
  , (' ', AP Nop)
  , ('!', AP Store)
  , ('*', AP Mul)
  , ('+', AP Add)
  , (',', AP Comma)
  , ('-', AP Minus)
  , ('.', AP Emit)
  , ('0', AP Zero)
  , ('1', AP One)
  , (':', AP SetTabEntry)
  , (';', AP CompileRet)
  , ('<', AP LessThan)
  , ('=', AP Equal)
  , ('>', AP CompileComma)
  , ('?', AP Dispatch)
  , ('@', AP Fetch)
  , ('A', AP CrashOnlyDuringStartup)
  , ('B', AP Branch0)
  , ('C', AP C_Fetch)
  , ('D', AP Dup)
  , ('E', AP EntryComma)
  , ('G', AP XtNext)
  , ('H', AP HerePointer)
  , ('I', AP IsImmediate)
  , ('J', AP Jump)
  , ('L', AP Lit)
  , ('M', AP CR)
  , ('N', AP XtName)
  , ('O', AP Over)
  , ('P', AP Drop)
  , ('V', AP Execute)
  , ('W', AP Swap)
  , ('X', AP Exit)
  , ('Y', AP IsHidden)
  , ('Z', AP Latest)
  , ('^', AP Key)
  , ('`', AP C_Comma)
  ]

type Mem = Map Addr Slot

mem0 :: Mem
mem0 = Map.fromList ([ (AP p, SlotPrim p) | p <- allPrims ]
                     ++ [(AN 0, SlotLit (VA (AN 1)))]
                    )
  where allPrims = [minBound..maxBound]

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

data Slot
  = SlotPrim Prim
  | SlotCall Addr
  | SlotRet
  | SlotLit Value
  | SlotChar Char

data Value = VC Char | VN Numb | VA Addr deriving (Eq)

type Numb = Word16

data Addr = AP Prim | AN Numb
  deriving (Eq,Ord)

instance Show Slot where
  show = \case
    SlotPrim p -> printf "*%s" (show p)
    SlotCall a -> printf "*%s" (show a)
    SlotRet -> printf "*ret"
    SlotLit v -> printf "#%s" (show v)
    SlotChar c -> printf "#'\\%02x'" (Char.ord c)

instance Show Value where
  show = \case
    VC c -> printf "'%c'" c
    VN n -> printf "%d" n
    VA a -> show a

instance Show Addr where
  show = \case
    AP p -> printf "&%s" (show p)
    AN n -> printf "&%d" n

nextAddr :: Addr -> Addr
nextAddr = \case
  AN i -> AN (i+1)
  a -> error (show ("nextAddr",a))

offsetAddr :: Addr -> Value -> Addr
offsetAddr a v = case a of
  AN i -> AN (i + numbOfValue v)
  a -> error (show ("offsetAddr",a))

valueOfSlot :: Slot -> Value
valueOfSlot = \case
  SlotLit v -> v
  slot -> error (printf "unexpected non-value slot: %s" (show slot))

charOfSlot :: Slot -> Char
charOfSlot = \case
  SlotChar c -> c
  slot -> error (printf "unexpected non-char slot: %s" (show slot))

isZero :: Value -> Bool
isZero v = numbOfValue v == 0

valueMinus :: Value -> Value -> Value
valueMinus v1 v2 = valueOfNumb (numbOfValue v1 - numbOfValue v2)

valueAdd :: Value -> Value -> Value
valueAdd v1 v2 = valueOfNumb (numbOfValue v1 + numbOfValue v2)

valueMul :: Value -> Value -> Value
valueMul v1 v2 = valueOfNumb (numbOfValue v1 * numbOfValue v2)

valueEqual :: Value -> Value -> Value
valueEqual v1 v2 = valueOfBool (numbOfValue v1 == numbOfValue v2)

valueLessThan :: Value -> Value -> Value
valueLessThan v1 v2 = valueOfBool (numbOfValue v1 < numbOfValue v2)

valueOfBool :: Bool -> Value
valueOfBool = VN . \case True -> vTrue; False-> vFalse
  where vTrue = (0 - 1); vFalse = 0

valueOfChar :: Char -> Value
valueOfChar = VC

charOfValue :: Value -> Char
charOfValue = \case
  VC c -> c
  VN n -> Char.chr (fromIntegral (n `mod` 256)) -- TODO: dodgy?
  v -> error (show ("charOfValue",v))

valueOfAddr :: Addr -> Value
valueOfAddr = VA

addrOfValue :: Value -> Addr
addrOfValue = \case VA a -> a ; v -> error (show ("addrOfValue",v))

valueOfNumb :: Numb -> Value
valueOfNumb = VN

numbOfValue :: Value -> Numb
numbOfValue = \case
  VC c -> fromIntegral (ord c)
  VN n -> n
  VA (AN n) -> n
  VA (AP p) -> error (show ("numbOfValue/AP",p))
