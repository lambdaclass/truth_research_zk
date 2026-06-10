import TRZK.ArithExpr

namespace TRZK

/-- Scalar element type for parameters, return values, and const-table entries.
    Only `.u32` ships today (BabyBear); step 2.5 (`Field F`) widens this. -/
inductive ScalarType where
  | u32
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-- Return type of a `Function`: a single scalar (arith specs) or a
    fixed-length array (matrix specs return all `m·n` cells as `[u32; N]`). -/
inductive RetTy where
  | scalar : ScalarType → RetTy
  | array  : ScalarType → Nat → RetTy
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-- Function body: one of the two shapes the current `Emit` already handles.
    `.scalar` carries a single `ArithExpr` (arith specs); `.cells` carries one
    `ArithExpr` per output cell (matrix specs), emitted as an array literal. -/
inductive FunctionBody where
  | scalar : ArithExpr → FunctionBody
  | cells  : List ArithExpr → FunctionBody
  deriving Repr, BEq, Hashable, Inhabited

/-- A compile-time constant table, emitted as a top-level Rust `const NAME:
    [TY; N] = [...];`. `values` holds canonical residues; `elemTy` selects the
    Rust array element type. Decoupling the two keeps the structure
    field-agnostic even though only u32 ships today. -/
structure ConstTable where
  name   : String
  elemTy : ScalarType
  values : Array Nat
  deriving Repr, BEq, Hashable, Inhabited

/-- A single emitted Rust function: positional `params` named `x0..`, a return
    type, and a body. The entry function emits as `pub fn`; helpers in
    `Program.functions` emit private. -/
structure Function where
  name   : String
  params : List (String × ScalarType)
  retTy  : RetTy
  body   : FunctionBody
  deriving Repr, BEq, Hashable, Inhabited

/-- File-level emission unit: compile-time constant tables, private helper
    functions, and one public entry-point function. Single-function specs wrap
    trivially with empty `tables` and `functions`. -/
structure Program where
  tables    : List ConstTable
  functions : List Function
  entry     : Function
  deriving Repr, BEq, Hashable, Inhabited

end TRZK
