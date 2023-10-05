
module Top (main) where -- TODO: split the one file implementation

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
  putStrLn "*tc-quarter*"
  xs <- sequence
    [ readFile ("../quarter-forth/f/" ++ f)
    | f <-
        [ "quarter.q"
{-        , "forth.f"
        , "tools.f"
        , "regression.f"
        , "examples.f"
        , "primes.f"
        , "start.f" -}
        ]
    ]
  go (concat xs)


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
  | Sp
  | Sp0
  | ReturnStackPointer
  | ReturnStackPointerBase
  | GetKey
  | Time
  | StartupIsComplete
  | EchoOn
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
  , ("sp", Sp)
  , ("sp0", Sp0)
  , ("rsp", ReturnStackPointer)
  , ("rsp0", ReturnStackPointerBase)
  , ("get-key", GetKey)
  , ("time", Time)
  , ("startup-is-complete", StartupIsComplete)
  , ("echo-on", EchoOn)
  ]

go :: String -> IO ()
go s = do
  let e = kernelEffect
  let m = machine0
  let i = runEff m e
  runInteraction s i

data Interaction
  = IHalt Machine
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
      IHalt _m@Machine{tick} -> do
        --printf "Remaining input: '%s'\n" inp
        printf "#machine-ticks=%d\n" tick
        printf "\n%s\n" (seeFinalMachine _m)
      IError s _m -> do
        printf "\n**Error: %s\n" s
        --printf "\n%s\n" (seeFinalMachine _m)
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
  v <- RPop
  exec (addrOfValue v)

prim1 :: Prim -> Eff ()
prim1 = \case
  Kdx_K -> do
    RPush (valueOfAddr (AP Kdx_D))
    prim Key
  Kdx_D -> do
    RPush (valueOfAddr (AP Kdx_X))
    prim Dispatch
  Kdx_X -> do
    RPush (valueOfAddr (AP Kdx_K))
    prim Execute
  Key -> do
    c <- Get
    Push (valueOfChar c)
  Dispatch -> do
    v <- Pop
    a <- LookupDT (charOfValue v)
    Push (valueOfAddr a)
  SetTabEntry -> do
    c <- Get
    a <- Here
    UpdateDT c a
  Execute -> do
    v <- Pop
    exec (addrOfValue v)
  Exit -> do
    _ <- RPop
    pure ()
  Jump -> do
    _ <- RPop
    v <- Pop
    RPush v
  Emit -> do
    v <- Pop
    Put (charOfValue v)
  CR -> do
    E_CR
  Nop -> do
    pure ()
  HerePointer -> do
    a <- HereAddr
    Push (valueOfAddr a)
  CompileComma -> do
    v <- Pop
    let slot = SlotCall (addrOfValue v)
    a <- Here
    Allot (slotSize slot)
    UpdateMem a slot
  RetComma -> do
    let slot = SlotRet
    a <- Here
    Allot (slotSize slot)
    UpdateMem a slot
  Comma -> do
    v <- Pop
    let slot = SlotLit v
    a <- Here
    Allot (slotSize slot)
    UpdateMem a slot
  C_Comma -> do
    v <- Pop
    let slot = SlotChar (charOfValue v)
    a <- Here
    Allot (slotSize slot)
    UpdateMem a slot
  Lit -> do
    a <- addrOfValue <$> RPop
    slot <- LookupMem a
    let v = valueOfSlot slot
    let a' = offsetAddr (slotSize slot) a
    Push v
    RPush (valueOfAddr a')
  Branch0 -> do
    a <- addrOfValue <$> RPop
    slot <- LookupMem a
    v <- Pop
    let n = fromIntegral $ numbOfValue (valueOfSlot slot)
    let a' = offsetAddr (if isZero v then n else slotSize slot) a
    RPush (valueOfAddr a')
  Branch -> do
    a <- addrOfValue <$> RPop
    slot <- LookupMem a
    let n = fromIntegral $ numbOfValue (valueOfSlot slot)
    let a' = offsetAddr n a
    RPush (valueOfAddr a')
  Fetch -> do
    v1 <- Pop
    slot <- LookupMem (addrOfValue v1)
    Push (valueOfSlot slot)
  C_Fetch -> do
    v1 <- Pop
    slot <- LookupMem (addrOfValue v1)
    Push (valueOfChar (charOfSlot slot))
  Store -> do
    a <- addrOfValue <$> Pop
    v <- Pop
    UpdateMem a (SlotLit v)
    -- For regression test which checks endian-ness:
    -- UpdateMem (offsetAddr 1 a) (SlotChar (Char.chr (fromIntegral (numbOfValue v) `div` 256)))
  C_Store -> do
    vLoc <- Pop
    v <- Pop
    UpdateMem (addrOfValue vLoc) (SlotChar (charOfValue v))
  Dup -> do
    v <- Pop
    Push v
    Push v
  Swap -> do
    v1 <- Pop
    v2 <- Pop
    Push v1
    Push v2
  Over -> do
    v1 <- Pop
    v2 <- Pop
    Push v2
    Push v1
    Push v2
  Drop -> do
    _ <- Pop
    pure ()
  Zero -> do
    Push (valueOfNumb 0)
  One -> do
    Push (valueOfNumb 1)
  Minus -> do
    v2 <- Pop
    v1 <- Pop
    Push (valueMinus v1 v2)
  Add -> do
    v2 <- Pop
    v1 <- Pop
    Push (valueAdd v1 v2)
  Mul -> do
    v2 <- Pop
    v1 <- Pop
    Push (valueMul v1 v2)
  Equal -> do
    v2 <- Pop
    v1 <- Pop
    Push (valueEqual v1 v2)
  LessThan -> do
    v2 <- Pop
    v1 <- Pop
    Push (valueLessThan v1 v2)
  Xor -> do
    v2 <- Pop
    v1 <- Pop
    Push (valueXor v1 v2)
  EntryComma -> do
    name <- addrOfValue <$> Pop
    next <- E_Latest
    let slot = SlotEntry Entry { name, next, hidden = False, immediate = False }
    a <- Here
    Allot (slotSize slot)
    UpdateMem a slot
    h <- Here
    SetLatest h -- we point to the XT, not the entry itself
  XtToNext -> do
    v1 <- Pop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{next} = entryOfSlot slot
    Push (valueOfAddr next)
  XtToName -> do
    v1 <- Pop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{name} = entryOfSlot slot
    Push (valueOfAddr name)
  Latest -> do
    a <- E_Latest
    Push (valueOfAddr a)
  IsHidden -> do
    v1 <- Pop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{hidden} = entryOfSlot slot
    Push (valueOfBool hidden)
  IsImmediate -> do
    v1 <- Pop
    slot <- LookupMem (prevAddr (addrOfValue v1))
    let Entry{immediate} = entryOfSlot slot
    Push (valueOfBool immediate)
  CrashOnlyDuringStartup -> do
    Abort "CrashOnlyDuringStartup"
  Crash -> do
    Abort "Crash"
  FlipImmediate -> do
    a <- (prevAddr . addrOfValue) <$> Pop
    entry@Entry{immediate} <- entryOfSlot <$> LookupMem a
    UpdateMem a (SlotEntry entry { immediate = not immediate })
  FlipHidden -> do
    a <- (prevAddr . addrOfValue) <$> Pop
    entry@Entry{hidden} <- entryOfSlot <$> LookupMem a
    UpdateMem a (SlotEntry entry { hidden = not hidden })
  FromReturnStack -> do
    b <- RPop
    a <- RPop
    Push a
    RPush b
  ToReturnStack -> do
    b <- RPop
    a <- Pop
    RPush a
    RPush b
  DivMod -> do
    b <- Pop
    a <- Pop
    let (d,m) = valueDivMod a b
    Push m
    Push d
  KeyNonBlocking -> do
    undefined
  BitShiftRight -> do
    a <- Pop
    Push (valueShiftRight a)
  Sp0 -> do
    Push (valueOfAddr paramStackBase)
  Sp -> do
    a <- StackPointer
    Push (valueOfAddr a)
  ReturnStackPointer -> do
    undefined
  ReturnStackPointerBase -> do
    undefined
  GetKey -> do
    Push (valueOfAddr (AP Key))
  Time -> do
    Push (valueOfNumb 123) -- TODO
    Push (valueOfNumb 456) -- TODO
  StartupIsComplete -> do
    pure () -- TODO
  EchoOn -> do
    pure () -- TODO


paramStackBase :: Addr
paramStackBase = AN 0

exec :: Addr -> Eff ()
exec = \case
  AP p -> prim p
  a0 -> do
    LookupMem a0 >>= \case
      slot@(SlotCall a) -> do
        RPush (valueOfAddr (offsetAddr (slotSize slot) a0))
        exec a
      SlotRet -> do
        v <- RPop
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
  Push :: Value -> Eff ()
  Pop :: Eff Value
  StackPointer :: Eff Addr
  RPush :: Value -> Eff ()
  RPop :: Eff Value
  E_Latest :: Eff Addr
  SetLatest :: Addr -> Eff ()
  HereAddr :: Eff Addr
  Here :: Eff Addr
  Allot :: Int -> Eff ()

runEff :: Machine -> Eff () -> Interaction
runEff m e = loop m e k0
  where
    k0 :: () -> Machine -> Interaction
    k0 () m = IHalt m

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
      UpdateMem (a@AS{}) _ -> IError (show ("UpdateMem",a)) m
      LookupMem a -> do
        let Machine{mem} = m
        case Map.lookup a mem of
          Just x -> k x m
          Nothing -> IError (show ("lookupMem",a)) m
      UpdateMem a x -> do
        let Machine{mem} = m
        k () m { mem = Map.insert a x mem }
      Push v -> do
        let Machine{pstack,sp,mem} = m
        let sp' = offsetAddr (-2) sp
        k () m { pstack = v:pstack
               , sp = sp', mem = Map.insert sp' (SlotLit v) mem
               }
      Pop -> do
        let Machine{pstack,sp,mem} = m
        case pstack of
          [] -> error "Pop[]"
          _:pstack -> do
            let v = valueOfSlot (maybe undefined id $ Map.lookup sp mem)
            k v m { pstack, sp = offsetAddr 2 sp }
      StackPointer -> do
        let Machine{sp} = m
        k sp m
      RPush v -> do
        let Machine{rstack} = m
        k () m { rstack = v:rstack }
      RPop -> do
        let Machine{rstack} = m
        case rstack of
          [] -> error "RPop[]"
          v:rstack -> k v m { rstack }
      E_Latest -> do
        let Machine{latest} = m
        k latest m
      SetLatest latest -> do
        k () m { latest }
      HereAddr -> do
        k addrOfHere m
      Here -> do
        let Machine{mem} = m
        let err = error "Here"
        let slot = maybe err id $ Map.lookup addrOfHere mem
        k (addrOfValue (valueOfSlot slot)) m
      Allot n -> do
        let Machine{mem} = m
        let err = error "Allot"
        let slot = maybe err id $ Map.lookup addrOfHere mem
        let a = addrOfValue (valueOfSlot slot)
        let a' = offsetAddr n a
        let slot' = SlotLit (valueOfAddr a')
        k () m { mem = Map.insert addrOfHere slot' mem }


data Machine = Machine
  { pstack :: [Value] -- TODO: kill
  , sp :: Addr
  , rstack :: [Value]
  , dispatchTable :: Map Char Addr
  , mem :: Map Addr Slot
  , tick :: Int
  , latest :: Addr
  }

instance Show Machine where
  show Machine{pstack=_p,rstack=_r} = do
    -- TODO show param-stack using sp/mem
    printf "%s ; %s" (show (reverse _p)) (show _r)

seeFinalMachine :: Machine -> String
seeFinalMachine m@Machine{mem=_mem} =
  unlines [ ""
          --, show m
          -- , dumpMem _mem
          , dumpDispatchTable m
          , tcSomething m
          ]

machine0 :: Machine
machine0 = Machine
  { pstack = []
  , sp = paramStackBase
  , rstack = []
  , dispatchTable =
      Map.fromList [ (c,AP p)
                   | (c,p) <- quarterDispatch ]
  , mem = mem0
  , tick = 0
  , latest = AP $ snd (head kernelDictionary)
  }

type Mem = Map Addr Slot

hereStart :: Addr
hereStart = AN 0

mem0 :: Mem
mem0 = Map.fromList $
       [(addrOfHere, SlotLit (VA hereStart))]
       ++ primEntries
  where
    primEntries :: [(Addr, Slot)]
    primEntries =
      [ (APE prim,
         SlotEntry Entry { name = AS name, next, hidden = False, immediate = False }
        )
      | ((name,prim),next) <-
        zip kernelDictionary $ [ AP prim | (_,prim) <- tail kernelDictionary ] ++ [ AN 0 ]
      ]

dumpDispatchTable :: Machine -> String
dumpDispatchTable Machine{dispatchTable=dt,mem} =
  unlines
  [ printf "%s : %s" (seeChar c) (unwords (map seeSlot slots))
  | (n,c) <- Map.toList userQDefs
  , c == '~' -- TODO: temp. just see the def of ~
  , let slots = collectDef [] (AN n)
  ]
  where
    collectDef :: [Slot] -> Addr -> [Slot]
    collectDef acc a =
      case Map.lookup a mem of
        Nothing -> error (show ("collectDef/addr",a))
        Just slot -> do
          let a' = offsetAddr (slotSize slot) a
          case slot of
            SlotRet -> reverse (slot:acc)
            _ -> collectDef (slot:acc) a'

    -- special case address which are in the dispatchTable
    seeSlot :: Slot -> String
    seeSlot = \case
      SlotCall (AN n) -> seeUserQ n
      SlotLit v -> printf "#%s" (seeValue v)
      slot -> show slot

    seeValue :: Value -> String
    seeValue = \case
      VA (AN n) -> seeUserQ n
      v -> show v

    seeUserQ :: Numb -> String
    seeUserQ n =
      case Map.lookup n userQDefs of
        Just c -> seeChar c
        Nothing -> show n

    -- Reverse mapping of user-generated defs
    userQDefs :: Map Numb Char
    userQDefs = Map.fromList [ (n,c) | (c,AN n) <- Map.toList dt ]


{-
dumpMem :: Mem -> String
dumpMem mem = do
  unlines
    [ printf "%s : %s" (show a) (unwords (map show slots))
    | (a,slots) <- collectDefs a0 a0 []
    ]
  where
    a0 = hereStart

    collectDefs :: Addr -> Addr -> [Slot] -> [(Addr,[Slot])]
    collectDefs a0 a acc =
      case Map.lookup a mem of
        Nothing -> [(a0,reverse acc)]
        Just slot -> do
          let a' = offsetAddr (slotSize slot) a
          case slot of
            SlotRet -> do
              (a0,reverse (slot:acc)) : collectDefs a' a' []
            _ ->
              collectDefs a0 a' (slot:acc)
-}

slotSize :: Slot -> Int
slotSize = \case
  SlotRet -> 1
  SlotCall{} -> 3
  SlotLit{} -> 2
  SlotChar{} -> 1
  SlotEntry{} -> 1
  SlotString{} -> undefined -- whatever!

data Slot
  = SlotRet
  | SlotCall Addr
  | SlotLit Value
  | SlotChar Char
  | SlotEntry Entry
  | SlotString String

data Entry = Entry
  { name :: Addr
  , next :: Addr
  , hidden :: Bool
  , immediate :: Bool
  }

data Value = VC Char | VN Numb | VA Addr deriving (Eq)

type Numb = Word16

data Addr = AN Numb | AP Prim | APE Prim | AS String | AH -- | AHplus1
  deriving (Eq,Ord)

instance Show Slot where
  show = \case
    SlotCall a -> printf "*%s" (show a)
    SlotRet -> printf "ret"
    SlotLit v -> printf "#%s" (show v)
    SlotChar c -> printf "#%s" (seeChar c)
    SlotEntry e -> show e
    SlotString s -> show s

instance Show Entry where
  -- dont bother to show the next-link or the hidden flag
  show Entry{name,next=_,hidden=_,immediate} =
    printf "[Entry:%s%s]" (stringOfAddr name) (if immediate then "(I)" else "")

stringOfAddr :: Addr -> String
stringOfAddr = \case
  AS s -> show s
  a -> show a

instance Show Value where
  show = \case
    VC c -> seeChar c
    VN n -> show n
    VA a -> show a

instance Show Addr where
  show = \case
    AN n -> printf "%d" n
    AP p -> printf "%s" (show p)
    APE p -> printf "Entry:%s" (show p)
    AS s -> printf "%s" (show s)
    AH -> printf "here"
    -- AHplus1 -> printf "(&here+1)"

prevAddr :: Addr -> Addr -- used only to skip back over entry slots
prevAddr = \case
  AN i -> AN (i-1) -- assumes an entry has size 1
  AP p -> APE p
  a -> error (show ("prevAddr",a))

offsetAddr :: Int -> Addr -> Addr
offsetAddr n a = case a of
  AN i -> AN (fromIntegral n + i)
  -- AH -> AHplus1
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
  --SlotLit v -> Char.chr (fromIntegral (numbOfValue v `mod` 256))
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
  _ -> False

valueMinus :: Value -> Value -> Value
valueMinus v1 v2 = valueOfNumb (numbOfValue v1 - numbOfValue v2)

valueAdd :: Value -> Value -> Value
valueAdd v1 v2 =
  case (v1,v2) of
    (VA (AS (_:s)),VN 1) -> VA (AS s) -- OMG, such a hack
    _ ->
      valueOfNumb (numbOfValue v1 + numbOfValue v2)

valueMul :: Value -> Value -> Value
valueMul v1 v2 = valueOfNumb (numbOfValue v1 * numbOfValue v2)

valueEqual :: Value -> Value -> Value
valueEqual v1 v2 = valueOfBool (numbOfValue v1 == numbOfValue v2)

valueLessThan :: Value -> Value -> Value
valueLessThan v1 v2 = valueOfBool (numbOfValue v1 `lessThen` numbOfValue v2)
  where
    lessThen :: Numb -> Numb -> Bool
    lessThen a b = mkSigned a < mkSigned b
      where
        mkSigned :: Numb -> Int
        mkSigned n = if n >= 0x8000 then fromIntegral n - 0x10000 else fromIntegral n


valueXor :: Value -> Value -> Value
valueXor v1 v2 = valueOfNumb (numbOfValue v1 `xor` numbOfValue v2)

valueDivMod :: Value -> Value -> (Value,Value)
valueDivMod v1 v2 = do
  ( valueOfNumb (numbOfValue v1 `div` numbOfValue v2) ,
    valueOfNumb (numbOfValue v1 `mod` numbOfValue v2) )

valueShiftRight :: Value -> Value
valueShiftRight v1 = valueOfNumb (numbOfValue v1 `div` 2)

valueOfBool :: Bool -> Value
valueOfBool = VN . \case True -> vTrue; False-> vFalse
  where vTrue = (0 - 1); vFalse = 0

valueOfChar :: Char -> Value
valueOfChar = VC

charOfValue :: Value -> Char
charOfValue = \case
  VC c -> c
  VN n -> Char.chr (fromIntegral (n `mod` 256))
  v -> error (show ("charOfValue",v))

valueOfAddr :: Addr -> Value
valueOfAddr = VA

addrOfHere :: Addr
addrOfHere = AH

addrOfValue :: Value -> Addr
addrOfValue = \case
  VA a -> a
  VN n -> AN n
  v@VC{} -> error (show ("addrOfValue",v))

valueOfNumb :: Numb -> Value
valueOfNumb = VN

numbOfValue :: Value -> Numb
numbOfValue = \case
  VC c -> fromIntegral (ord c)
  VN n -> n
  VA (AN n) -> n
  a -> error (show ("numbOfValue",a))

seeChar :: Char -> String
seeChar c = if
  | n>=32 && n<=126 -> printf "'%c'" c
  | otherwise -> printf "'\\%02x'" n
  where n = Char.ord c

----------------------------------------------------------------------
-- Type Checking...

tcSomething :: Machine -> String
tcSomething Machine{dispatchTable=dt,mem} = do

  let aTilda = maybe undefined id (Map.lookup '~' dt) -- that something is the ~ definition
  let slots = collectSlots [] aTilda
  seeRes (runInfer (tcSlotsExec slots))

  where

    seeRes :: Either TypeError (TyEffect,Subst) -> String
    seeRes = \case
      Left e ->
        printf "~ :: ERROR: %s" (show e) -- TODO: use coorrect name
      Right (eff,subst) -> do
        let sub = useSubst subst
        unlines [ printf "~ :: %s" (show eff)
                , printf "SUB: %s" (show subst)
                , printf "APP: %s" (show (subEffect sub eff))
                ]

    look :: Addr -> Slot
    look a = maybe undefined id (Map.lookup a mem)

    collectSlots :: [Slot] -> Addr -> [Slot]
    collectSlots acc a = do
      let slot = look a
      let a' = offsetAddr (slotSize slot) a
      case slot of
        SlotRet -> reverse (slot:acc)
        _ -> collectSlots (slot:acc) a'


tcSlotsExec :: [Slot] -> Infer TyEffect
tcSlotsExec = \case
  [] -> pure effect0
  slot1:slots -> do
    e1 <- tcSlotExec slot1
    e2 <- tcSlotsExec slots
    sub <- CurrentSub
    let e1' = subEffect sub e1
    let e2' = subEffect sub e2
    composeEffect e1' e2'

tcSlotExec :: Slot -> Infer TyEffect
tcSlotExec slot = case slot of
  SlotCall a -> tcAddrExec a
  SlotRet -> pure effect0
  SlotLit{} -> nope
  SlotChar{} -> nope
  SlotEntry{} -> nope
  SlotString{} -> nope
  where
    nope = Nope (printf "tcSlotExec: %s" (show slot))

effect0 :: TyEffect
effect0 = TE_effect m m
  where
    m = TM { stack = s }
    s = TS_var (TVar 99) -- TODO: fresh

tcAddrExec :: Addr -> Infer TyEffect
tcAddrExec = \case
  AP p -> tcPrimExec p
  AN n -> undefined n
  APE p -> undefined p
  AS s -> undefined s
  AH -> undefined

-- TODO: primitives should be bound to type schemes!
-- which we instantiate with fresh vars at each use occurancex
tcPrimExec :: Prim -> Infer TyEffect
tcPrimExec = \case

  Key -> pure (TE_effect m1 m2)
    where
      m1 = TM { stack = s1 }
      m2 = TM { stack = TS_cons s1 T_num }
      s1 = TS_var (TVar 11) -- TODO : fresh

  Dispatch -> pure (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons s1 T_num }
      m2 = TM { stack = TS_cons s1 (T_addr (TA_xt e1)) }
      s1 = TS_var (TVar 22)
      e1 = TE_effect TM { stack = TS_exists "S1" } TM { stack = TS_exists "S2" }

  CompileComma -> pure (TE_effect m1 m2)
    where
      m1 = TM { stack = TS_cons s1 (T_addr (TA_xt e1)) }
      m2 = TM { stack = s1 }
      s1 = TS_var (TVar 33)
      e1 = TE_effect TM { stack = TS_var (TVar 34) } TM { stack = TS_var (TVar 35) }

  p ->
    error (show ("tcPrimExec",p))


data TyEffect -- type of a machine effect (currently just stack effect)
  = TE_effect TyMachine TyMachine

composeEffect :: TyEffect -> TyEffect -> Infer TyEffect
composeEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m2 m3
      pure (TE_effect m1 m4)

subEffect :: Sub -> TyEffect -> TyEffect
subEffect sub = \case
    TE_effect m1 m2 ->
      TE_effect (subMachine sub m1) (subMachine sub m2)

unifyEffect :: TyEffect -> TyEffect -> Infer ()
unifyEffect e1 e2 = do
  case (e1,e2) of
    (TE_effect m1 m2, TE_effect m3 m4) -> do
      unifyMachine m1 m3
      unifyMachine m2 m4


data TyMachine = TM
  { stack :: TyStack -- currently just the type of the stack
  -- TODO: we also need the return statck
  -- TODO: and we need info relating to here/compiling
  }

subMachine :: Sub -> TyMachine -> TyMachine
subMachine sub = \case
  TM{stack} -> TM { stack = subStack sub stack }

unifyMachine :: TyMachine -> TyMachine -> Infer ()
unifyMachine m1 m2 = do
  case (m1,m2) of
    (TM{stack=s1},TM{stack=s2}) ->
      unifyStack s1 s2


data TyStack
  = TS_cons TyStack TyValue
--  | TS_empty
  | TS_var TVar
  | TS_exists String -- existential state. you dont get to pick! skolem?

subStack :: Sub -> TyStack -> TyStack
subStack sub = loop
  where
    loop :: TyStack -> TyStack
    loop = \case
      TS_cons s v ->
        TS_cons (loop s) (subValue sub v)
      stack@(TS_var var) ->
        case applySub sub var of
          Nothing -> stack
          Just replacement -> replacement
      stack@TS_exists{} ->
        stack

unifyStack :: TyStack -> TyStack -> Infer ()
unifyStack s1 s2 =
  case (s1,s2) of
    (TS_var var, stack) -> InfSubst var stack
    (stack, TS_var var) -> InfSubst var stack
    (TS_cons s1 v1, TS_cons s2 v2) -> do
      unifyStack s1 s2
      unifyValue v1 v2
    (TS_cons{}, _) -> Nope "cons/?"
    (_, TS_cons{}) -> Nope "?/cons"
    (TS_exists x1, TS_exists x2) -> if (x1 == x2) then pure () else Nope "?/?"


data TyValue -- the type of a 16-bit value, or cell. things which can be stack items
  = T_num -- 16 bit numeric value; may be a char/bool
  | T_addr TyAddr -- 16 bit address of something
--  | T_var Int

subValue :: Sub -> TyValue -> TyValue
subValue sub = \case
  T_num -> T_num
  T_addr a -> T_addr (subAddr sub a)

unifyValue :: TyValue -> TyValue -> Infer ()
unifyValue v1 v2 =
  case (v1,v2) of
    (T_num,T_num) -> pure ()
    (T_num,T_addr{}) -> Nope "num/addr"
    (T_addr{},T_num) -> Nope "addr/num"
    (T_addr a1, T_addr a2) -> unifyAddr a1 a2


data TyAddr -- the type of the slot at an address
  = TA_xt TyEffect -- slot containg XT with an effect
--  | TA_call TyEffect -- ( s -- s' ) slot containing call with effect
--  | TA_char -- char* -- slot containing a char
--  | TA_lit TyValue -- T* -- slot containing a 16-bit value
  -- No variable here!

subAddr :: Sub -> TyAddr -> TyAddr
subAddr sub = \case
  TA_xt e -> TA_xt (subEffect sub e)

unifyAddr :: TyAddr -> TyAddr -> Infer ()
unifyAddr a1 a2 =
  case (a1,a2) of
    (TA_xt e1, TA_xt e2) -> unifyEffect e1 e2


instance Show TyEffect where
  show = \case
    TE_effect m1 m2 ->
      printf "(%s -- %s)" (show m1) (show m2)

instance Show TyMachine where
  show = \case
    TM{stack} -> show stack

instance Show TyStack where
  show = \case
    TS_cons s v -> printf "%s %s" (show s) (show v)
    TS_var n -> show n
    TS_exists x -> x

instance Show TyValue where
  show = \case
    T_num{} -> "N"
    T_addr a -> show a

instance Show TyAddr where
  show = \case
    TA_xt e -> printf "XT%s" (show e)

instance Show TVar where
  show (TVar n) = printf "%s" (show n)


instance Functor Infer where fmap = liftM
instance Applicative Infer where pure = InfReturn; (<*>) = ap
instance Monad Infer where (>>=) = InfBind

data Infer a where
  InfReturn :: a -> Infer a
  InfBind :: Infer a -> (a -> Infer b) -> Infer b
  InfSubst :: TVar -> TyStack -> Infer ()
  Nope :: String -> Infer a
  CurrentSub :: Infer Sub

type InfRes a = Either TypeError (a,Subst)

runInfer :: Infer a -> InfRes a
runInfer inf0 = loop subst0 inf0 k0
  where
    k0 :: a -> Subst -> InfRes a
    k0 a s = Right (a,s)

    loop :: Subst -> Infer a -> (a -> Subst -> InfRes b) -> InfRes b
    loop s inf k = case inf of
      InfReturn x -> do
        k x s
      InfBind m f -> do
        loop s m $ \a s -> loop s (f a) k
      InfSubst v stack -> do
        k () (extendSubst s v stack)
      Nope s -> do
        Left (TypeError (printf "Nope: %s" s))
      CurrentSub -> do
        k (useSubst s) s


data Sub = Sub (TVar -> Maybe TyStack) -- functional rep

applySub :: Sub -> TVar -> Maybe TyStack
applySub (Sub f) = f


data Subst = Subst (Map TVar TyStack)

useSubst :: Subst -> Sub
useSubst (Subst m) = Sub (\v -> Map.lookup v m)

subst0 :: Subst
subst0 = Subst Map.empty

extendSubst :: Subst -> TVar -> TyStack -> Subst
extendSubst (Subst m) key replacement = do
  let g = Sub (\v -> if v==key then Just replacement else Nothing)
  let mShifted = Map.map (subStack g) m
  Subst (Map.insert key replacement mShifted)


data TVar = TVar Int -- currently only stacks can be variable
  deriving (Eq,Ord)

data TypeError = TypeError String

deriving instance Show TypeError
deriving instance Show Subst
