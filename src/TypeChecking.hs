
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
  ( Scheme(..), makeScheme
  , Trans(..)
  , Machine(..)
  , Stack(..)
  , Elem(..)
  , Numeric(..)
  , Contents(..)
  , svarsOfStack
  , evarsOfElem
  , (~~>), (~), xt, num, addr, addr_char, mkSVar, mkEVar
  )

import Infer
  ( Infer(..), runInfer
  , instantiateScheme
  , subStack, subElem
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

----------------------------------------------------------------------
-- Primitives

schemeOfPrim :: Prim -> Maybe Scheme
schemeOfPrim = \case

  Key -> scheme $ s1 ~~> (s1 ~ num)

  Dispatch -> scheme $ (s1 ~ num) ~~> (s1 ~ xt (S_Skolem "S1" ~~> S_Skolem "S2"))

  CompileComma -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> s1

  Over -> scheme $ (s1 ~ e1 ~ e2) ~~> (s1 ~ e1 ~ e2 ~ e1)

  Dup -> scheme $ (s1 ~ e1) ~~> (s1 ~ e1 ~ e1)

  Swap -> scheme $ (s1 ~ e1 ~ e2) ~~> (s1 ~ e2 ~ e1)

  Minus -> scheme $ (s1 ~ e1 ~ e1) ~~> (s1 ~ num) -- TODO: only allow numerics!
  --Minus -> scheme $ (s1 ~ num ~ num) ~~> (s1 ~ num) -- TODO: more general - any numerics!

  HerePointer -> scheme $ s1 ~~> (s1 ~ addr (addr e1))

  Fetch -> scheme $ (s1 ~ addr e1) ~~> (s1 ~ e1)
  C_Fetch -> scheme $ (s1 ~ addr_char) ~~> (s1 ~ num)

  Store -> scheme $ (s1 ~ e1 ~ addr e1) ~~> s1

  One -> scheme $ s1 ~~> (s1 ~ num)
  Zero -> scheme $ s1 ~~> (s1 ~ num) -- TODO: more general

  --Add -> scheme $ (s1 ~ num ~ num) ~~> (s1 ~ num) -- TODO: more general - any numerics
  Add -> scheme $ (s1 ~ e1 ~ num) ~~> (s1 ~ e1) -- TODO: too general - TC's 'q'

  Branch0 -> scheme $ (s1 ~ num) ~~> s1 -- pops one elem

  Lit -> scheme $ s1 ~~> (s1 ~ e1) -- pushes one elem -- TODO: e1 should be skolem

  Jump -> scheme $ (s1 ~ xt(s1 ~~> s2)) ~~> s2

  Drop -> scheme $ s1 ~ e1 ~~> s1

  Emit -> scheme $ s1 ~ num ~~> s1

  Comma -> scheme $ s1 ~ num ~~> s1 -- overly specific
  C_Comma -> scheme $ s1 ~ num ~~> s1

  Equal -> scheme $ (s1 ~ e1 ~ e1) ~~> (s1 ~ num)
  LessThan -> scheme $ (s1 ~ e1 ~ e1) ~~> (s1 ~ num)

  IsHidden -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ num)
  IsImmediate -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ num)
  XtToNext -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ xt (s4 ~~> s5)) -- skolem!

  Execute -> scheme $ (s1 ~ xt(s1 ~~> s2)) ~~> s2

  CR -> scheme $ (s1 ~~> s1)
  CrashOnlyDuringStartup -> scheme $ (s1 ~~> s1)

  Latest -> scheme $ s1 ~~> (s1 ~ xt (S_Skolem "S1" ~~> S_Skolem "S2"))

  XtToName -> scheme $ (s1 ~ xt (s2 ~~> s3)) ~~> (s1 ~ addr_char)

  RetComma -> scheme $ (s1 ~~> s1)

  _ -> Nothing

  where
    scheme = Just . makeScheme

    s1 = mkSVar 11
    s2 = mkSVar 22
    s3 = mkSVar 33
    s4 = mkSVar 44
    s5 = mkSVar 55

    e1 = mkEVar 111
    e2 = mkEVar 222

tcPrim1 :: Prim -> Infer Trans
tcPrim1 prim =
  case schemeOfPrim prim of
    Nothing -> Nope (printf "tcPrim1: %s" (show prim))
    Just scheme -> do
      t <- instantiateScheme scheme
      --Message (printf "%s:: %s" (show prim) (show t))
      pure t

----------------------------------------------------------------------
-- unify*

unifyTrans :: Trans -> Trans -> Infer ()
unifyTrans t1 t2 = do
  case (t1,t2) of
    (T_Trans m1 m2, T_Trans m3 m4) -> do
      unifyMachine m1 m3
      unifyMachine m2 m4

unifyMachine :: Machine -> Machine -> Infer ()
unifyMachine m1 m2 = do
  case (m1,m2) of
    (Machine{stack=s1},Machine{stack=s2}) ->
      unifyStack s1 s2

unifyStack :: Stack -> Stack -> Infer ()
unifyStack s1x s2x = do
  sub <- CurrentSub
  let s1 = subStack sub s1x
  let s2 = subStack sub s2x
  let nope = Nope (printf "stack mismatch: %s ~ %s" (show s1) (show s2))
  let cyclic = Nope (printf "stack cyclic: %s ~ %s" (show s1) (show s2))
  case (subStack sub s1, subStack sub s2) of

    (S_Var x1, stack@(S_Var x2)) ->
      if x1==x2 then pure () else SubStack x1 stack

    (S_Var x, stack) ->
      if x `elem` svarsOfStack stack then cyclic else SubStack x stack

    (stack, S_Var x) ->
      if x `elem` svarsOfStack stack then cyclic else SubStack x stack

    (S_Cons s1 e1, S_Cons s2 e2) -> do
      unifyStack s1 s2
      unifyElem e1 e2

    (S_Cons{}, _) -> nope
    (_, S_Cons{}) -> nope
    (S_Skolem x1, S_Skolem x2) ->
      -- TODO: can we regard a skolem as not even the same as itself?
      if (x1 == x2) then pure () else nope


unifyElem :: Elem -> Elem -> Infer ()
unifyElem e1x e2x = do
  sub <- CurrentSub
  let e1 = subElem sub e1x
  let e2 = subElem sub e2x
  let nope = Nope (printf "elem mismatch: %s ~ %s" (show e1) (show e2))
  let cyclic = Nope (printf "elem cyclic: %s ~ %s" (show e1) (show e2))
  case (e1, e2) of

    (E_Var x1, el@(E_Var x2)) ->
      if x1==x2 then pure () else SubElem x1 el

    (E_Var x, el) ->
      if x `elem` evarsOfElem el then cyclic else SubElem x el

    (el, E_Var x) ->
      if x `elem` evarsOfElem el then cyclic else SubElem x el

    (E_Numeric n1, E_Numeric n2) -> unifyNumeric n1 n2
    (E_XT t1, E_XT t2) -> unifyTrans t1 t2

    (E_Numeric{},E_XT{}) -> nope
    (E_XT{},E_Numeric{}) -> nope

unifyNumeric :: Numeric -> Numeric -> Infer ()
unifyNumeric a1 a2 =
  case (a1,a2) of
    (N_Number, N_Number) -> pure ()
    (N_Address c1, N_Address c2) -> unifyContents c1 c2

    (N_Number, N_Address{}) -> nope
    (N_Address{}, N_Number) -> nope
  where
    nope = Nope (printf "unifyNumeric: %s ~ %s" (show a1) (show a2))

unifyContents :: Contents -> Contents -> Infer ()
unifyContents c1 c2 =
  case (c1,c2) of
    (C_Char,C_Char) -> pure ()
    (C_Elem e1, C_Elem e2) -> unifyElem e1 e2

    (C_Char, C_Elem{}) -> nope
    (C_Elem{}, C_Char) -> nope
  where
    nope = Nope (printf "unifyContents: %s ~ %s" (show c1) (show c2))
