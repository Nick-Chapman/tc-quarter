
module TypeChecking
  ( tcStart -- used in Testing types of dispatch tabel entries
  , tc, Tenv(..), tenv0, lookupTenv, Subst, subTS
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
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Contents(..)
  , (~~>), (~), num, xt, addr
  )

import PrimTyping (typeOfPrim)

import Infer
  ( Infer(..)
  , runInfer
  , instantiateScheme, canonicalizeScheme
  , Subst, subTrans, subElem
  )

import Unify
  ( unifyTrans
  , unifyMachine
  )

import Execution (Loc(..))

tcStart :: X.State -> Char -> Infer Trans
tcStart xstate@X.State{dispatchTable=dt} c = do
  case Map.lookup c dt of
    Nothing -> do
      error (printf "no dispatch table entry for %s" (seeChar c))
    Just a -> do
      (ts,_) <- tcAddr xstate tenv0 a
      case ts of
        TS_Trans ty -> pure ty
        _ -> do
          error "dispatch table entry defined as non code"


tc :: X.State -> Tenv -> Addr -> IO (Tenv,Subst)
tc xstate te@Tenv{u,last,nErrs} high = do
  --printf "**tc: %s -- %s\n" (show last) (show high)
  let
    X.State{mem} = xstate
  let
    look :: Addr -> Slot
    look a = maybe err id (Map.lookup a mem)
      where err = error (show ("tc/look",a))
  let
    collectSlots :: Addr -> [(Addr,Slot)]
    collectSlots a = do
      if a == high then [] else do
        let slot = look a
        let a' = offsetAddr (slotSize slot) a
        (a,slot) : collectSlots a'
  let _slots = collectSlots last

  let
    X.State{locs} = xstate
    locate :: Addr -> Loc
    locate a = maybe noloc id (Map.lookup a locs)
      where noloc = Loc "" 1 0

  --print ("tc:",_slots)
  (errs,res) <- runInfer (locate last) u (tcRange xstate te last high)

  let
    reportTypeError = True

  when reportTypeError $
    sequence_ [ printf "** TypeError: %s\n" (show e) | e <- errs ]

  case res of
    (u,subst,te1) -> do
      let te2 = subTenv subst te1 -- TODO: can we avoid this?
      -- print (te2) -- TODO: see the growing tenv
      pure
        ( te2
          { last = high
          , u
          , nErrs = length errs + nErrs
          }
        , subst
        )

data TS -- Type of a slot
  = TS_Trans Trans
  | TS_Elem Elem
  | TS_Char
  | TS_Entry

instance Show TS where
  show = \case
    TS_Trans tr -> show (canonicalizeScheme (makeScheme tr))
    TS_Elem el -> show el
    TS_Char -> "Char"
    TS_Entry -> "Entry"

subTS :: Subst -> TS -> TS
subTS sub = \case
  TS_Trans tr -> TS_Trans (subTrans sub tr)
  TS_Elem tr -> TS_Elem (subElem sub tr)
  TS_Char -> TS_Char
  TS_Entry -> TS_Entry

data Tenv = Tenv
  { u :: Int -- Hack for threading fres var counter
  , last :: Addr
  , m :: Map Addr TS -- TODO: Trans --> new type Slot
  , nErrs :: Int
  }

instance Show Tenv where
  show Tenv{m} = do
    unlines
      [ printf "%s : %s" (show a) (show ts)
      | (a,ts) <- Map.toList m
      ]

tenv0 :: Tenv
tenv0 = Tenv { last = AN 0, m = Map.empty, u = 0, nErrs = 0 }

subTenv :: Subst -> Tenv -> Tenv -- TODO: must we do this??
subTenv sub te@Tenv{m} =
  te { m = Map.map (subTS sub) m }

updateTenv :: Addr -> TS -> Tenv -> Tenv
updateTenv a v te@Tenv{m} = te { m = Map.insert a v m }

lookupTenv :: Addr -> Tenv -> TS
lookupTenv a Tenv{m} =
  case Map.lookup a m of
    Just x -> x
    Nothing -> error (show ("lookupTenv",a))

tcRange :: X.State -> Tenv -> Addr -> Addr -> Infer Tenv
tcRange xstate te a aHigh = do -- TODO: loop, pick up aHigh from scope
  if a>=aHigh then pure te else do
    (_,te') <- tcAddr xstate te a
    tcRange xstate te' (nextSlotAddr xstate a) aHigh

tcAddr :: X.State -> Tenv -> Addr -> Infer (TS,Tenv) -- TODO: gen contents
tcAddr xstate@X.State{mem} te@Tenv{m} a = do
  --Message (show ("tcAddr",a))
  case Map.lookup a m of
    Just contents -> do
      pure (contents,te)
    Nothing -> do
      case Map.lookup a mem of
        Nothing -> do
          --error (show ("tcAddr: no slot at address",a)) -- snake/allot
          let ts = TS_Elem num -- hack
          pure (ts,te)
        Just slot -> do
          --Message (show ("tcAddr",a,slot,"..."))
          (ts,te1) <- tcSlot xstate te a slot
          --Message (printf "%s: %s\t\t%s" (show a) (show slot) (show ts))
          let te2 = updateTenv a ts te1
          pure (ts,te2)


tcSlot :: X.State -> Tenv -> Addr -> Slot -> Infer (TS,Tenv)
tcSlot xstate te a0 slot = do
  --Message (show ("tcSlot",a0,slot))
  case slot of
    SlotLit v -> do
      elem <- tcLitValue xstate te v
      pure (TS_Elem elem, te)
    SlotChar{} -> do
      pure (TS_Char, te)
    SlotEntry{} -> do
      pure (TS_Entry, te)
    SlotString{} ->
      error "SlotString" -- TODO
    SlotRet -> do
      trans <- noTrans
      pure (TS_Trans trans, te)
    SlotCall callAddr -> do

      -- HACK TO BREAK RECURSION
      stack <- S_Var <$> FreshS
      let m = Machine { stack }
      let tsV = TS_Trans (T_Trans m m)
      let te0 = updateTenv a0 tsV te

      let a1 = offsetAddr (slotSize slot) a0
      (trans1,next,te1) <- tcCall xstate te0 a1 callAddr
      case next of
        Next0 -> do
          pure (TS_Trans trans1,te1)
        Next1 a2 -> do
          (ts2,te2) <- tcAddr xstate te1 a2 -- TODO: use shadowing for te
          case ts2 of
            TS_Trans trans2 -> do
              trans <- composeTrans trans1 trans2
              pure (TS_Trans trans,te2)
            _ -> do
              error (printf "fallthrough to non-code at address: %s" (show a2))
        Next2 a2 a3 -> do
          (ts2,te2) <- tcAddr xstate te1 a2
          (ts3,te3) <- tcAddr xstate te2 a3
          case (ts2,ts3) of
            (TS_Trans trans2, TS_Trans trans3) -> do
              --Message (show ("unifyTrans:",trans2,trans3))
              unifyTrans trans2 trans3
              trans <- composeTrans trans1 trans2
              pure (TS_Trans trans,te3)
            (TS_Trans{},_) -> do
              error (printf "branch to non-code at address: %s" (show a3))
            (_,_) -> do
              error (printf "fallthrough to non-code at address: %s" (show a2))

data Next = Next0 | Next1 Addr | Next2 Addr Addr


tcLitValue :: X.State -> Tenv -> Value -> Infer Elem
tcLitValue xstate te = \case
  VN{} -> pure num
  VC{} -> pure num
  VA addr -> litAddr xstate te addr

litAddr :: X.State -> Tenv -> Addr -> Infer Elem
litAddr _xstate _te = \case -- TODO: dont need these args
  AP prim -> do
    trans <- tcPrim1 prim
    pure (xt trans)
  AN{} -> do
    c <- C_Var <$> FreshC -- TODO: unify this with anything?
    pure (addr c)

  a -> do
    let _ = (num,xt)
    error (printf "litAddr: %s" (show a))



tcCall :: X.State -> Tenv -> Addr -> Addr -> Infer (Trans,Next,Tenv)
tcCall xstate te a1 codeAddr = do
  let nope = error (printf "tcCall: %s" (show codeAddr))
  case codeAddr of
    APE{} -> nope
    AS{} -> nope
    AH{} -> nope
    AN{} -> do
      (ts,te) <- tcAddr xstate te codeAddr
      case ts of
        TS_Trans trans -> do
          -- TODO: generalize here?? -- YES, this was what was preventing TC
          trans <- instantiateScheme $ makeScheme trans

          pure (trans, Next1 a1, te)
        _ -> do
          error (printf "calling non-code at address: %s" (show codeAddr))


    AP prim ->
      tcPrim xstate te a1 prim


tcPrim :: X.State -> Tenv -> Addr -> Prim -> Infer (Trans,Next,Tenv)
tcPrim xstate te a1 = \case
  Lit -> do
    (ts,te1) <- tcAddr xstate te a1
    case ts of
      TS_Elem elem -> do
        stack <- S_Var <$> FreshS
        let trans = stack ~~> (stack ~ elem)
        pure (trans, Next1 (nextSlotAddr xstate a1), te1)
      _ ->
        error (printf "unexpected non-literal-cell at address: %s" (show a1))

  Branch0 -> do
    trans <- tcPrim1 Branch0
    let (a2,a3) = getBranchDests xstate a1
    pure (trans, Next2 a2 a3, te)

  Branch -> do
    trans <- tcPrim1 Branch
    let (_,a3) = getBranchDests xstate a1
    pure (trans, Next1 a3, te)

  Exit -> do
    trans <- noTrans -- TODO: call tcPrim1?
    pure (trans, Next0, te)

  Jump -> do
    trans <- tcPrim1 Jump
    pure (trans,Next0, te)

  prim  -> do
    ty <- tcPrim1 prim
    pure (ty, Next1 a1, te)


nextSlotAddr :: X.State -> Addr -> Addr
nextSlotAddr X.State{mem} a =
  case Map.lookup a mem of
    Nothing ->
      --error (show ("nextSlotAddr: no slot at address",a)) --snake/allot
      offsetAddr 1 a -- hack
    Just slot ->
      offsetAddr (slotSize slot) a


composeTrans :: Trans -> Trans -> Infer Trans
composeTrans e1 e2 = do
  case (e1,e2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      --Message "unifyMachine..."
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
