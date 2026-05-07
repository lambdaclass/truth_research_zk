import TRZK.Field.BabyBear

namespace TRZK

/-- Arithmetic AST. The surface type users write specs in.

    Constants live in the BabyBear field. Step 1 carries the field as a single
    fixed type; step 2.5 generalises to a field type parameter. Op set is
    field-relevant only — `idiv`, `shl`, `shr` are out of scope at this layer
    (shifts return in step 2 as representation-aware ops; integer division has
    no field analog). -/
inductive ArithExpr where
  | const : BabyBear → ArithExpr
  | var   : Nat → ArithExpr
  | add   : ArithExpr → ArithExpr → ArithExpr
  | sub   : ArithExpr → ArithExpr → ArithExpr
  | neg   : ArithExpr → ArithExpr
  | mul   : ArithExpr → ArithExpr → ArithExpr
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Number of AST nodes. -/
def ArithExpr.size : ArithExpr → Nat
  | .const _ => 1
  | .var _   => 1
  | .add a b => 1 + a.size + b.size
  | .sub a b => 1 + a.size + b.size
  | .neg a   => 1 + a.size
  | .mul a b => 1 + a.size + b.size

/-- Positional input arity: one more than the largest var index, or 0 if no
    vars. Computed pre-optimization so codegen preserves the source signature
    even when rules eliminate variable references (e.g. `a - a => 0`). -/
def ArithExpr.inputArity : ArithExpr → Nat
  | .const _ => 0
  | .var i   => i + 1
  | .add a b => Nat.max a.inputArity b.inputArity
  | .sub a b => Nat.max a.inputArity b.inputArity
  | .neg a   => a.inputArity
  | .mul a b => Nat.max a.inputArity b.inputArity

end TRZK
