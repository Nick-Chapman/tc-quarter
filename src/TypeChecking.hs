
module TypeChecking
  ( tcMachine -- used in Top
  , tcStart   -- used in Testing
  ) where

import Data.Map (Map)
import Prim (Prim(..))
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Execution as X(State(..))

import Execution
  ( Slot(..), Addr(..)
  , Numb
  , seeChar
  , offsetAddr, slotSize
  , numbOfValue
  , Value(..)
  )

import Types
  ( makeScheme
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , (~~>), (~), num
  )

import PrimTyping (typeOfPrim)

import Infer
  ( Infer(..), runInfer
  , instantiateScheme
  )

import Unify
  ( unifyTrans
  , unifyMachine
  )

tcMachine :: X.State -> IO ()
tcMachine m@X.State{dispatchTable=dt,mem} = do
  let _all = [ x | (_,x) <- Map.toList userQDefs ]
  mapM_ tcDef _all
  where
    tcDef :: Char -> IO ()
    tcDef c = do
      let _slots = slotsForDef c
      --printf "%s : %s\n" (seeChar c) (unwords (map _seeSlot _slots))
      either <- runInfer (tcStart m c)
      case either of
        Left e -> do
          printf "%s :: ERROR: %s\n" (seeChar c) (show e)
        Right ty ->
          printf "%s :: %s\n" (seeChar c) (show ty)

    look :: Addr -> Slot
    look a = maybe undefined id (Map.lookup a mem)

    slotsForDef :: Char -> [Slot]
    slotsForDef c = do
      let a = maybe undefined id (Map.lookup c dt)
      collectSlots [] a

    collectSlots :: [Slot] -> Addr -> [Slot]
    collectSlots acc a = do
      let slot = look a
      let a' = offsetAddr (slotSize slot) a
      case slot of
        SlotRet -> reverse (slot:acc)
        _ -> collectSlots (slot:acc) a'

    -- special case address which are in the dispatchTable
    _seeSlot :: Slot -> String
    _seeSlot = \case
      SlotCall (AN n) -> printf "*%s" (seeUserQ n)
      --SlotLit v -> printf "#%s" (seeValue v)
      slot -> show slot

    _seeValue :: Value -> String
    _seeValue = \case
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

----------------------------------------------------------------------

tcStart :: X.State -> Char -> Infer Trans
tcStart m@X.State{dispatchTable=dt,mem} c = do
  case Map.lookup c dt of
    Nothing ->
      Nope (printf "no dispatch table entry for %s" (seeChar c))
    Just (AN n) -> do
      aVars <- Map.fromList <$> sequence
        [ do
            s1 <- S_Var <$> FreshS
            s2 <- S_Var <$> FreshS
            let trans = s1 ~~> s2
            pure (n,trans)
        | (_,AN n) <- Map.toList dt
        ]
      loopA aVars n
    Just{} -> do
      Nope (printf "non-user dispatch table entry for %s" (seeChar c))

 where
  loopA :: Map Numb Trans -> Numb -> Infer Trans
  loopA aVars n = do
    t1 <- loop (AN n)
    let t2 = getAddrVar n
    unifyTrans t1 t2
    pure t1

   where

    getAddrVar :: Numb -> Trans
    getAddrVar n =
       case Map.lookup n aVars of
         Nothing -> error "lookup-aVars failed"
         Just tr -> tr

    loop :: Addr -> Infer Trans
    loop a = do
      --Message (printf "loop: %s" (show a))
      (t1,as) <- tcAddr a
      --Message (printf "loop: %s: %s" (show a) (show t1))
      case as of
        [] ->
          pure t1

        [a] -> do
          t2 <- loop a
          composeTrans t1 t2

        [aX,aY] -> do
          t2 <- loop aX
          t2' <- loop aY
          unifyTrans t2 t2'
          composeTrans t1 t2
        _ ->
          undefined

    tcAddr :: Addr -> Infer (Trans, [Addr])
    tcAddr a = do
      case Map.lookup a mem of
        Nothing ->
          Nope (printf "tcAddr: nothing at address %s" (show a))
        Just slot ->
          tcSlot (offsetAddr (slotSize slot) a) slot

    tcSlot :: Addr -> Slot -> Infer (Trans,[Addr])
    tcSlot a slot = do
      let nope tag = Nope (printf "tcSlot(%s): %s" tag (show slot))
      case slot of
        SlotLit{} -> nope "lit"
        SlotChar{} -> nope "char"
        SlotEntry{} -> nope "entry"
        SlotString{} -> nope "string"
        SlotRet -> do
          t <- noTrans
          pure (t,[])
        SlotCall callAddr ->
          tcCall a callAddr

    tcCall :: Addr -> Addr -> Infer (Trans,[Addr])
    tcCall a callAddr = do
      let nope = Nope (printf "tcCall: %s" (show callAddr))
      case callAddr of
        APE{} -> nope
        AS{} -> nope
        AH{} -> nope

        AN n -> do
          -- TODO: calling sub defs -- need to maintain somekind of type env
          -- currently we just get an unbound trans of from : s1 -- s2
          let trans = getAddrVar n
          pure (trans, [a])

        AP prim ->
          tcPrim a prim

    tcPrim :: Addr -> Prim -> Infer (Trans,[Addr])
    tcPrim a = \case
      Exit -> do
        trans <- noTrans
        pure (trans,[])
      Jump -> do
        trans <- tcPrim1 Jump
        pure (trans,[])
      Branch0 -> do
        trans <- tcPrim1 Branch0
        let (a1,a2) = getBranchDests m a
        pure (trans, [a1,a2])
      Lit -> do
        let (value,a') = expectLit m a
        elem <- tcLitValue value
        stack <- S_Var <$> FreshS
        let trans = stack ~~> (stack ~ elem)
        pure (trans, [a'])
      prim -> do
        trans <- tcPrim1 prim
        pure (trans,[a])

    tcLitValue :: Value -> Infer Elem
    tcLitValue = \case
      VN{} -> pure num
      VC{} -> pure num -- needed for standard def of '('
      VA addr -> do
        litAddr addr

    litAddr :: Addr -> Infer Elem
    litAddr = \case
      AP prim -> do
        trans <- tcPrim1 prim
        pure (E_XT trans)
      AN n -> do
        pure (E_XT (getAddrVar n))
      a ->
        Nope (printf "litAddr: %s" (show a))


getBranchDests :: X.State -> Addr -> (Addr,Addr)
getBranchDests X.State{mem} a =
  case Map.lookup a mem of
    Nothing ->
      error (printf "doBranch: nothing at address %s" (show a))
    Just slot ->
      case slot of
        SlotLit v -> do
          let n = fromIntegral $ numbOfValue v
          (offsetAddr 2 a, offsetAddr n a)
        _ ->
          error (printf "doBranch: unexpected non-lit slot after Branch0 %s"
                 (show slot))


expectLit :: X.State -> Addr -> (Value,Addr)
expectLit X.State{mem} a =
  case Map.lookup a mem of
    Nothing ->
      error (printf "expectLit: nothing at address %s" (show a))
    Just slot ->
      case slot of
        SlotLit lit -> (lit, offsetAddr (slotSize slot) a)
        _ ->
          error (printf "expectLit: unexpected non-lit slot: %s" (show (a,slot)))

composeTrans :: Trans -> Trans -> Infer Trans
composeTrans e1 e2 = do
  case (e1,e2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      unifyMachine m2 m3
      pure (T_Trans m1 m4)

noTrans :: Infer Trans
noTrans = do
  x <- FreshS
  let s = S_Var x
  let m = Machine { stack = s }
  pure (T_Trans m m)

tcPrim1 :: Prim -> Infer Trans
tcPrim1 prim = do
  let scheme = makeScheme (typeOfPrim prim)
  instantiateScheme scheme
