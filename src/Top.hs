
module Top (main) where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (ap,liftM)
import Data.Word (Word16)
import Text.Printf (printf)
import Data.Char as Char (chr,ord)
import Data.Bits (xor)
import System.IO (hFlush,stdout)

main :: IO ()
main = do
  putStrLn "*spec-quarter*"
  xs <- sequence
    [ readFile ("/home/nic/code/quarter-forth/f/"++f)
    | f <-
        [ "quarter.q"
        , "forth.f"
        , "tools.f"
        , "examples.f"
        , "primes.f"
        ]
    ]
--  go (concat xs ++ " 1 2 3 .s cr 4 5 6 .s cr ")
  go (concat xs ++ " z cr char A char B char C rot . cr . cr . cr ")

data Prim
  = Kdx_K | Kdx_D | Kdx_X -- TODO: meh
  | Key | Dispatch | SetTabEntry
  | Execute | Exit | Jump
  | Emit | CR | Nop
  | HerePointer
  | CompileComma | RetComma | Comma | C_Comma
  | Lit | Branch0 | Branch
  | Fetch | Store
  | C_Fetch
  | Dup | Swap | Over | Drop
  | Zero | One | Minus | Add | Mul | Equal | LessThan | Xor
  | EntryComma | XtToNext | XtToName | Latest | IsHidden | IsImmediate
  | Crash
  | CrashOnlyDuringStartup
  -- Not in dispatch table; available in dictionary only
  | FlipImmediate
  | FlipHidden
  | FromReturnStack
  | ToReturnStack
  | DivMod
  | KeyNonBlocking
  | C_Store
  | BitShiftRight
  | StackPointer
  | StackPointerBase
  | ReturnStackPointer
  | ReturnStackPointerBase
  | GetKey
  deriving (Eq,Ord,Show,Enum,Bounded)

quarterDispatch :: [(Char,Prim)]
quarterDispatch =
  [ ('\n',Nop)
  , (' ', Nop)
  , ('!', Store)
  , ('*', Mul)
  , ('+', Add)
  , (',', Comma)
  , ('-', Minus)
  , ('.', Emit)
  , ('0', Zero)
  , ('1', One)
  , (':', SetTabEntry)
  , (';', RetComma)
  , ('<', LessThan)
  , ('=', Equal)
  , ('>', CompileComma)
  , ('?', Dispatch)
  , ('@', Fetch)
  , ('A', CrashOnlyDuringStartup)
  , ('B', Branch0)
  , ('C', C_Fetch)
  , ('D', Dup)
  , ('E', EntryComma)
  , ('G', XtToNext)
  , ('H', HerePointer)
  , ('I', IsImmediate)
  , ('J', Jump)
  , ('L', Lit)
  , ('M', CR)
  , ('N', XtToName)
  , ('O', Over)
  , ('P', Drop)
  , ('V', Execute)
  , ('W', Swap)
  , ('X', Exit)
  , ('Y', IsHidden)
  , ('Z', Latest)
  , ('^', Key)
  , ('`', C_Comma)
  ]

kernelDictionary :: [(String,Prim)]
kernelDictionary =
  [ ("immediate^", FlipImmediate)
  , ("latest", Latest)
  , ("lit", Lit)
  , (",", Comma)
  , ("compile,", CompileComma)
  , ("jump", Jump)
  , ("here-pointer", HerePointer)
  , ("@", Fetch)
  , ("0", Zero)
  , ("dup", Dup)
  , ("swap", Swap)
  , ("-", Minus)
  , ("!", Store)
  , ("0branch", Branch0)
  , ("branch", Branch)
  , ("1", One)
  , ("+", Add)
  , ("*", Mul)
  , ("<", LessThan)
  , ("xor", Xor)
  , ("key", Key)
  , ("drop", Drop)
  , ("c,", C_Comma)
  , ("exit", Exit)
  , ("c@", C_Fetch)
  , ("=", Equal)
  , ("entry,", EntryComma)
  , ("ret,", RetComma)
  , ("r>", FromReturnStack)
  , ("emit", Emit)
  , ("execute", Execute)
  , ("cr", CR)
  , ("crash", Crash)
  , (">r", ToReturnStack)
  , ("hidden?", IsHidden)
  , ("xt->name", XtToName)
  , ("over", Over)
  , ("xt->next", XtToNext)
  , ("hidden^", FlipHidden)
  , ("/mod", DivMod)
  , ("key?", KeyNonBlocking)
  , ("c!", C_Store)
  , ("crash-only-during-startup", CrashOnlyDuringStartup)
  , ("immediate?", IsImmediate)
  , ("/2", BitShiftRight)
  , ("sp", StackPointer)
  , ("sp0", StackPointerBase)
  , ("rsp", ReturnStackPointer)
  , ("rsp0", ReturnStackPointerBase)
  , ("get-key", GetKey)
  ]

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
        printf "\n**Error: %s\n" s
        --printf "\n%s\n" (seeFinalMachine _m)
        pure ()
      IDebug m i -> do
        printf "%s\n" (show m)
        loop n inp i
      IDebugMem m i -> do
        printf "\n%s\n" (seeFinalMachine m)
        loop n inp i
      IMessage mes i -> do
        printf "**%s\n" mes
        loop n inp i
      ICR i -> do
        putStrLn ""
        loop n inp i
      IPut _c i -> do
        --printf "PUT: %c\n" _c
        _flush
        printf "%c" _c
        loop n inp i
      IGet f -> do
        case inp of
          [] -> loop (n+1) inp (f Nothing)
          c:inp -> do
            --printf "%c" c -- echo-on
            loop (n+1) inp (f (Just c))

    _flush = hFlush stdout


kernelEffect :: Eff ()
kernelEffect = prim Kdx_K

prim :: Prim -> Eff ()
prim p = do
  --Debug
  _i <- Tick
  --Message (printf " {%d} %s" _i (show p))
  prim1 p
  v <- RsPop
  exec (addrOfValue v)

prim1 :: Prim -> Eff ()
prim1 = \case
  Kdx_K -> do
    RsPush (valueOfAddr (AP Kdx_D))
    prim Key
  Kdx_D -> do
    RsPush (valueOfAddr (AP Kdx_X))
    prim Dispatch
  Kdx_X -> do
    RsPush (valueOfAddr (AP Kdx_K))
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
    RsPush v
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
  RetComma -> do
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
    a <- addrOfValue <$> RsPop
    slot <- LookupMem a
    let v = valueOfSlot slot
    let a' = nextAddr a
    PsPush v
    RsPush (valueOfAddr a')
  Branch0 -> do
    a <- addrOfValue <$> RsPop
    slot <- LookupMem a
    v <- PsPop
    let a' = if isZero v then offsetAddr a (valueOfSlot slot) else nextAddr a
    RsPush (valueOfAddr a')
  Branch -> do
    a <- addrOfValue <$> RsPop
    slot <- LookupMem a
    let a' = offsetAddr a (valueOfSlot slot)
    RsPush (valueOfAddr a')
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
  Xor -> do
    v2 <- PsPop
    v1 <- PsPop
    PsPush (valueXor v1 v2)
  EntryComma -> do
    name <- addrOfValue <$> PsPop
    next <- E_Latest
    let e = Entry { name, next, hidden = False, immediate = False }
    a <- bump
    UpdateMem a (SlotEntry e)
    h <- E_Here
    SetLatest h -- we point to the XT, not the entry itself
  XtToNext -> do
    v1 <- PsPop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{next} = entryOfSlot slot
    PsPush (valueOfAddr next)
  XtToName -> do
    v1 <- PsPop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{name} = entryOfSlot slot
    PsPush (valueOfAddr name)
  Latest -> do
    a <- E_Latest
    PsPush (valueOfAddr a)
  IsHidden -> do
    v1 <- PsPop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{hidden} = entryOfSlot slot
    PsPush (valueOfBool hidden)
  IsImmediate -> do
    v1 <- PsPop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{immediate} = entryOfSlot slot
    PsPush (valueOfBool immediate)
  CrashOnlyDuringStartup -> do
    Abort "CrashOnlyDuringStartup"
  Crash -> do
    Abort "Crash"
  FlipImmediate -> do
    a <- (prevAddr . addrOfValue) <$> PsPop
    entry@Entry{immediate} <- entryOfSlot <$> LookupMem a
    UpdateMem a (SlotEntry entry { immediate = not immediate })
  FlipHidden -> do
    a <- (prevAddr . addrOfValue) <$> PsPop
    entry@Entry{hidden} <- entryOfSlot <$> LookupMem a
    UpdateMem a (SlotEntry entry { hidden = not hidden })
  FromReturnStack -> do
    b <- RsPop
    a <- RsPop
    PsPush a
    RsPush b
    pure ()
  ToReturnStack -> do
    b <- RsPop
    a <- PsPop
    RsPush a
    RsPush b
  DivMod -> do
    b <- PsPop
    a <- PsPop
    let (d,m) = valueDivMod a b
    PsPush m
    PsPush d
  KeyNonBlocking -> do
    undefined
  C_Store -> do
    undefined
  BitShiftRight -> do
    a <- PsPop
    PsPush (valueShiftRight a)
  StackPointer -> do
    undefined
  StackPointerBase -> do
    undefined
  ReturnStackPointer -> do
    undefined
  ReturnStackPointerBase -> do
    undefined
  GetKey -> do
    PsPush (valueOfAddr (AP Key))


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
      RsPush (valueOfAddr (nextAddr a0))
      exec a
    SlotRet -> do
      v <- RsPop
      exec (addrOfValue v)
    SlotLit{} ->
      Abort "exec: SLotLit"
    SlotChar{} ->
      Abort "exec: SlotChar"
    SlotEntry{} -> do
      Abort "exec: SlotChar"
    SlotString{} ->
      Abort "exec: SlotString"

instance Functor Eff where fmap = liftM
instance Applicative Eff where pure = Return; (<*>) = ap
instance Monad Eff where (>>=) = Bind

data Eff a where
  Return :: a -> Eff a
  Bind :: Eff a -> (a -> Eff b) -> Eff b
  Debug :: Eff ()
  DebugMem :: Eff ()
  Message :: String -> Eff ()
  Abort :: String -> Eff ()
  Tick :: Eff Int
  Get :: Eff Char
  Put :: Char -> Eff ()
  E_CR :: Eff ()
  LookupDT :: Char -> Eff Addr
  UpdateDT :: Char -> Addr -> Eff ()
  LookupMem :: Addr -> Eff Slot
  UpdateMem :: Addr -> Slot -> Eff ()
  -- TODO: improve clarity of Ps/Rs
  -- rename -> Param/Return
  -- or maybe have no prefix for param-stack
  PsPush :: Value -> Eff ()
  PsPop :: Eff Value
  RsPush :: Value -> Eff ()
  RsPop :: Eff Value
  E_Latest :: Eff Addr
  SetLatest :: Addr -> Eff ()
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
      Abort mes -> IError mes m
      Tick -> do
        let Machine{tick} = m
        k tick m { tick = tick + 1 }
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
      LookupMem (AS s) -> k (SlotString s) m -- super duper special case
      LookupMem a -> do
        let Machine{mem} = m
        case Map.lookup a mem of
          Just x -> k x m
          Nothing -> IError (show ("lookupMem",a)) m
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
      RsPush v -> do
        let Machine{rstack} = m
        k () m { rstack = v:rstack }
      RsPop -> do
        let Machine{rstack} = m
        case rstack of
          [] -> error "RsPop[]"
          v:rstack -> k v m { rstack }
      E_Latest -> do
        let Machine{latest} = m
        k latest m
      SetLatest latest -> do
        k () m { latest }
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
  , rstack :: [Value]
  , dispatchTable :: Map Char Addr
  , mem :: Map Addr Slot
  , hereAddr :: Addr -- TODO: use special structured address
  , tick :: Int
  , latest :: Addr
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
  , dispatchTable =
      Map.fromList [ (c,AP p)
                   | (c,p) <- quarterDispatch ]
  , mem = mem0
  , hereAddr = AN 0
  , tick = 0
  , latest = AP $ snd (head kernelDictionary)
  }

type Mem = Map Addr Slot

mem0 :: Mem
mem0 = Map.fromList $
       [ (AP p, SlotPrim p) | p <- allPrims ]
       ++ [(AN 0, SlotLit (VA (AN 1)))] -- for here-pointer. TODO: yuck
       ++ primEntries
  where
    primEntries :: [(Addr, Slot)]
    primEntries =
      [ (APE prim,
         SlotEntry (Entry { name = AS name, next, hidden = False, immediate = False })
        )
      | ((name,prim),next) <-
        zip kernelDictionary $ [ AP prim | (_,prim) <- tail kernelDictionary ] ++ [ AN 0 ]
      ]
    allPrims = [minBound..maxBound]

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
  | SlotEntry Entry
  | SlotString String

data Entry = Entry
  { name :: Addr
  , next :: Addr
  , hidden :: Bool
  , immediate :: Bool
  } deriving Show

data Value = VC Char | VN Numb | VA Addr deriving (Eq)

type Numb = Word16

data Addr = AN Numb | AP Prim | APE Prim | AS String
  deriving (Eq,Ord)

instance Show Slot where
  show = \case
    SlotPrim p -> printf "*%s" (show p)
    SlotCall a -> printf "*%s" (show a)
    SlotRet -> printf "*ret"
    SlotLit v -> printf "#%s" (show v)
    SlotChar c -> printf "#%s" (seeChar c)
    SlotEntry e -> printf "[%s]" (show e)
    SlotString s -> show s

instance Show Value where
  show = \case
    VC c -> seeChar c
    VN n -> printf "%d" n
    VA a -> show a

instance Show Addr where
  show = \case
    AN n -> printf "&%d" n
    AP p -> printf "&%s" (show p)
    APE p -> printf "&Entry:%s" (show p)
    AS s -> printf "&%s" (show s)

nextAddr :: Addr -> Addr
nextAddr = \case
  AN i -> AN (i+1)
  a -> error (show ("nextAddr",a))

prevAddr :: Addr -> Addr
prevAddr = \case
  AN i -> AN (i-1)
  AP p -> APE p
  a@APE{} -> error (show ("prevAddr",a))
  a@AS{} -> error (show ("prevAddr",a))

offsetAddr :: Addr -> Value -> Addr
offsetAddr a v = case a of
  AN i -> AN (i + numbOfValue "offsetAddr" v)
  a -> error (show ("offsetAddr",a))

valueOfSlot :: Slot -> Value
valueOfSlot = \case
  SlotLit v -> v
  slot -> error (printf "unexpected non-value slot: %s" (show slot))

charOfSlot :: Slot -> Char
charOfSlot = \case
  SlotChar c -> c
  SlotString [] -> '\0'
  SlotString (c:_) -> c
  slot -> error (printf "unexpected non-char slot: %s" (show slot))

entryOfSlot :: Slot -> Entry
entryOfSlot = \case
  SlotEntry e -> e
  slot -> error (printf "unexpected non-entry slot: %s" (show slot))

isZero :: Value -> Bool
isZero = \case
  VC c ->  c == '\0'
  VN n -> n == 0
  VA (AN n) -> n == 0
  VA (AP{}) -> False
  VA (APE{}) -> False
  VA (AS{}) -> False

valueMinus :: Value -> Value -> Value
valueMinus v1 v2 = valueOfNumb (numbOfValue "-A" v1 - numbOfValue "-B" v2)

valueAdd :: Value -> Value -> Value
valueAdd v1 v2 =
  case (v1,v2) of
    (VA (AS (_:s)),VN 1) -> VA (AS s) -- OMG, such a hack
    _ ->
      valueOfNumb (numbOfValue "+A" v1 + numbOfValue "+B" v2)

valueMul :: Value -> Value -> Value
valueMul v1 v2 = valueOfNumb (numbOfValue "*A" v1 * numbOfValue "*B" v2)

valueEqual :: Value -> Value -> Value
valueEqual v1 v2 = valueOfBool (numbOfValue "=A" v1 == numbOfValue "=B" v2)

valueLessThan :: Value -> Value -> Value
valueLessThan v1 v2 = valueOfBool (numbOfValue "<A" v1 < numbOfValue "<B" v2)

valueXor :: Value -> Value -> Value
valueXor v1 v2 = valueOfNumb (numbOfValue "xA" v1 `xor` numbOfValue "xB" v2)

valueDivMod :: Value -> Value -> (Value,Value)
valueDivMod v1 v2 = do
  ( valueOfNumb (numbOfValue "dA" v1 `div` numbOfValue "dB" v2) ,
    valueOfNumb (numbOfValue "mA" v1 `mod` numbOfValue "mB" v2) )

valueShiftRight :: Value -> Value
valueShiftRight v1 = valueOfNumb (numbOfValue "sA" v1 `div` 2)

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
addrOfValue = \case
  VA a -> a
  VN n -> AN n -- TODO: hmm?
  v@VC{} -> error (show ("addrOfValue",v))

valueOfNumb :: Numb -> Value
valueOfNumb = VN

numbOfValue :: String -> Value -> Numb
numbOfValue tag = \case
  VC c -> fromIntegral (ord c)
  VN n -> n
  VA (AN n) -> n
  VA (AP p) -> error (show ("numbOfValue/AP",tag,p))
  VA (APE p) -> error (show ("numbOfValue/APE",tag,p))
  VA (AS s) -> error (show ("numbOfValue/AS",tag,s))

seeChar :: Char -> String
seeChar c = printf "'\\%02x'" (Char.ord c)
