
module Prim (Prim(..)) where

-- TODO: Make these Show as their kernel dictionary names.
-- and implement the kernel dict as the reverse lookup

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
  | EchoOff
  | EchoEnabled
  | SetCursorShape
  | SetCursorPosition
  | ReadCharCol
  | WriteCharCol
  | Cls
  | KEY
  | SetKey
  deriving (Eq,Ord,Show,Enum,Bounded)
