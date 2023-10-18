
module TypeChecking
  ( tcTestQuarterDef
  , tc -- main TC entry point
  , Tenv(..)
  , tenv0
  , lookupTenv
  ) where

import Control.Monad (when)
import Data.Map (Map)
import Prim (Prim(..))
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Execution as X(State(..))

import Execution
  ( Slot(..), Addr(..)
  , seeChar
  , offsetAddr, slotSize
  , numbOfValue
  , Value(..)
  )

import Types
  ( makeScheme
  , Trans (..)
  , Machine (..)
  , Elem
  , (~~>), (~), num, xt, addr
  )

import PrimTyping (typeOfPrim)

import Infer
  ( Infer
  , runInfer, reasonToInfer
  , TypeError
  , instantiateScheme, canonicalizeScheme
  , Subst, subTrans, subElem
  , freshStack, freshContents
  )

import Unify
  ( unifyTrans
  , unifyMachine
  )

import Execution (Loc(..))

tcTestQuarterDef :: Int -> X.State -> Char -> IO (Either TypeError Trans)
tcTestQuarterDef n xstate c = do
  let context = makeContext xstate
  let a = lookupDispatchTable context c
  let loc = Loc "test" n 0
  let u0 = 0
  (errs,(_,subst,(ts,_))) <- runInfer loc u0 (tcAddr context tenv0 a)
  case errs of
    err:_ -> pure (Left err)
    [] -> do
      case ts of
        SL_Trans trans -> do
          pure $ Right (canonicalizeScheme (makeScheme (subTrans subst trans)))
        _ ->
          error "dispatch table entry defined as non code"

tc :: X.State -> Tenv -> Addr -> IO (Tenv,Subst)
tc xstate te@Tenv{u,last,nErrs} high = do
  --printf "**tc: %s -- %s\n" (show last) (show high)
  let context = makeContext xstate
  let
    collectSlots :: Addr -> [(Addr,Slot)]
    collectSlots a = do
      if a == high then [] else do
        let slot = lookupAddrSlot context a
        let a' = offsetAddr (slotSize slot) a
        (a,slot) : collectSlots a'

  let _slots = collectSlots last
  --printf "\n%s\n" (show _slots)
  let loc = lookupAddrLocation context last
  (errs,res) <- runInfer loc u (tcRange context te last high)
  let
    reportTypeError = True
  when reportTypeError $
    sequence_ [ printf "** TypeError: %s\n" (show e) | e <- errs ]
  case res of
    (u,subst,te1) -> do
      let te2 = subTenv subst te1 -- TODO: can we avoid this?
      let res =
            ( te2
              { last = high
              , u
              , nErrs = length errs + nErrs
              }
            , subst
            )
      --printf "\n%s\n" (show te2)
      pure res


data Tenv = Tenv
  { u :: Int -- Hack for threading fresh var counter
  , last :: Addr
  , m :: Map Addr SlotType
  , nErrs :: Int
  }

instance Show Tenv where
  show Tenv{last,m} = do
    unlines
      [ printf "%s : %s" (show addr) (show trans)
      | (addr,trans) <- Map.toList m
      , addr >= last
      ]

tenv0 :: Tenv
tenv0 = Tenv { last = AN 0, m = Map.empty, u = 0, nErrs = 0 }

subTenv :: Subst -> Tenv -> Tenv -- TODO: must we do this??
subTenv sub te@Tenv{m} =
  te { m = Map.map (subSlotType sub) m }

lookupTenv :: Addr -> Tenv -> SlotType
lookupTenv a Tenv{m} =
  case Map.lookup a m of
    Just x -> x
    Nothing -> error (show ("lookupTenv",a))

data SlotType
  = SL_Trans Trans
  | SL_Elem Elem
  | SL_Char
  | SL_Entry

instance Show SlotType where
  show = \case
    SL_Trans tr -> show (canonicalizeScheme (makeScheme tr))
    SL_Elem el -> show el
    SL_Char -> "Char"
    SL_Entry -> "Entry"

subSlotType :: Subst -> SlotType -> SlotType
subSlotType sub = \case
  SL_Trans tr -> SL_Trans (subTrans sub tr)
  SL_Elem tr -> SL_Elem (subElem sub tr)
  SL_Char -> SL_Char
  SL_Entry -> SL_Entry

tcRange :: Context -> Tenv -> Addr -> Addr -> Infer Tenv
tcRange context te a aHigh = do
  if a>=aHigh then pure te else do
    (_,te') <- tcAddr context te a
    tcRange context te' (nextSlotAddr context a) aHigh

tcAddr :: Context -> Tenv -> Addr -> Infer (SlotType,Tenv)
tcAddr context te@Tenv{m} a = do
  case Map.lookup a m of
    Just contents -> do
      pure (contents,te)
    Nothing -> do
      case lookupAddrSlotMaybe context a of
        Nothing -> do -- snake/allot
          let ts = SL_Elem num -- hack?
          pure (ts,te)
        Just slot -> do
          (ts,te1) <- tcSlot context te a slot
          let te2 = updateTenv a ts te1
          pure (ts,te2)

updateTenv :: Addr -> SlotType -> Tenv -> Tenv
updateTenv a v te@Tenv{m} = te { m = Map.insert a v m }

tcSlot :: Context -> Tenv -> Addr -> Slot -> Infer (SlotType,Tenv)
tcSlot context te a0 slot = do
  case slot of
    SlotLit v -> do
      elem <- tcLitValue v
      pure (SL_Elem elem, te)
    SlotChar{} -> do
      pure (SL_Char, te)
    SlotEntry{} -> do
      pure (SL_Entry, te)
    SlotString{} ->
      error "SlotString"

    SlotRet -> do
      stack <- freshStack
      let m = Machine { stack }
      let trans = T_Trans m m
      pure (SL_Trans trans, te)

    SlotCall callAddr -> do

      -- HACK TO BREAK RECURSION
      stack <- freshStack
      let m = Machine { stack }
      let tsV = SL_Trans (T_Trans m m)
      let te0 = updateTenv a0 tsV te

      let a1 = offsetAddr (slotSize slot) a0
      (trans1,next,te1) <- tcCall context te0 a1 callAddr
      case next of
        Next0 -> do
          pure (SL_Trans trans1,te1)
        Next1 a2 -> do
          (ts2,te2) <- tcAddr context te1 a2 -- TODO: use shadowing for te
          case ts2 of
            SL_Trans trans2 -> do
              trans <- composeTrans trans1 trans2
              pure (SL_Trans trans,te2)
            _ -> do
              error (printf "fallthrough to non-code at address: %s" (show a2))
        Next2 a2 a3 -> do
          (ts2,te2) <- tcAddr context te1 a2
          (ts3,te3) <- tcAddr context te2 a3
          case (ts2,ts3) of
            (SL_Trans trans2, SL_Trans trans3) -> do
              reasonToInfer "branch0" $ do
              unifyTrans trans2 trans3
              trans <- composeTrans trans1 trans2
              pure (SL_Trans trans,te3)
            (SL_Trans{},_) -> do
              error (printf "branch to non-code at address: %s" (show a3))
            (_,_) -> do
              error (printf "fallthrough to non-code at address: %s" (show a2))

composeTrans :: Trans -> Trans -> Infer Trans
composeTrans e1 e2 = do
  case (e1,e2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      reasonToInfer "compose" $ do
      unifyMachine m2 m3
      pure (T_Trans m1 m4)

data Next = Next0 | Next1 Addr | Next2 Addr Addr

tcLitValue :: Value -> Infer Elem
tcLitValue = \case
  VN{} -> pure num
  VC{} -> pure num
  VA addr -> litAddr addr

litAddr :: Addr -> Infer Elem
litAddr = \case
  AP prim -> do
    trans <- tcPrim1 prim
    pure (xt trans)
  AN{} -> do
    c <- freshContents -- TODO: unify this with anything?
    pure (addr c)
  addr -> do
    error (printf "litAddr: %s" (show addr))

tcCall :: Context -> Tenv -> Addr -> Addr -> Infer (Trans,Next,Tenv)
tcCall context te a1 codeAddr = do
  let nope = error (printf "tcCall: %s" (show codeAddr))
  case codeAddr of
    APE{} -> nope
    AS{} -> nope
    AH{} -> nope
    AN{} -> do
      (ts,te) <- tcAddr context te codeAddr
      case ts of
        SL_Trans trans -> do
          trans <- instantiateScheme $ makeScheme trans
          pure (trans, Next1 a1, te)
        _ -> do
          error (printf "calling non-code at address: %s" (show codeAddr))
    AP prim ->
      tcPrim context te a1 prim

tcPrim :: Context -> Tenv -> Addr -> Prim -> Infer (Trans,Next,Tenv)
tcPrim context te a1 prim = do
  case prim of
    Lit -> do
      (ts,te1) <- tcAddr context te a1
      case ts of
        SL_Elem elem -> do
          stack <- freshStack
          let trans = stack ~~> (stack ~ elem)
          pure (trans, Next1 (nextSlotAddr context a1), te1)
        _ ->
          error (printf "unexpected non-literal-cell at address: %s" (show a1))
    Branch0 -> do
      trans <- tcPrim1 prim
      let (a2,a3) = getBranchDests context a1
      pure (trans, Next2 a2 a3, te)
    Branch -> do
      trans <- tcPrim1 prim
      let (_,a3) = getBranchDests context a1
      pure (trans, Next1 a3, te)
    Exit -> do
      trans <- tcPrim1 prim
      pure (trans, Next0, te)
    Jump -> do
      trans <- tcPrim1 prim
      pure (trans, Next0, te)
    _  -> do
      trans <- tcPrim1 prim
      pure (trans, Next1 a1, te)

tcPrim1 :: Prim -> Infer Trans
tcPrim1 prim = instantiateScheme (makeScheme (typeOfPrim prim))

nextSlotAddr :: Context -> Addr -> Addr
nextSlotAddr context addr = do
  let z = maybe 1 slotSize $ lookupAddrSlotMaybe context addr
  offsetAddr z addr

getBranchDests :: Context -> Addr -> (Addr,Addr)
getBranchDests context a =
  case lookupAddrSlotMaybe context a of
    Nothing ->
      error (printf "doBranch: nothing at address %s" (show a))
    Just _slot -> do
      let slot = lookupAddrSlot context a
      case slot of
        SlotLit v -> do
          let n = fromIntegral $ numbOfValue v
          (offsetAddr 2 a, offsetAddr n a)
        _ ->
          error (printf "doBranch: unexpected non-lit slot after Branch0 %s"
                 (show slot))

----------------------------------------------------------------------
-- Context

data Context = Context -- Downwards context when type checking
  { xstate :: X.State
  }

makeContext :: X.State -> Context
makeContext xstate = Context { xstate }

lookupDispatchTable :: Context -> Char -> Addr
lookupDispatchTable context c = do
  let Context{xstate=X.State{dispatchTable=dt}} = context
  case Map.lookup c dt of
    Nothing -> error (printf "no dispatch table entry for %s" (seeChar c))
    Just a -> a

lookupAddrSlot :: Context -> Addr -> Slot
lookupAddrSlot context addr = do
  maybe err id $ lookupAddrSlotMaybe context addr
    where err = error (printf "lookupAddrSlot: nothing at address %s" (show addr))

lookupAddrSlotMaybe :: Context -> Addr -> Maybe Slot
lookupAddrSlotMaybe context addr = do
  let Context{xstate=X.State{mem}} = context
  Map.lookup addr mem

lookupAddrLocation :: Context -> Addr -> Loc
lookupAddrLocation context a = do
  let Context{xstate=X.State{locs}} = context
  maybe noloc id (Map.lookup a locs)
    where noloc = Loc "" 1 0
