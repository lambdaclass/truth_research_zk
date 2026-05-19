import TRZK.Field.BabyBear

namespace TRZK

/-- Arithmetic AST. The surface type users write specs in.

    Constants are canonical-form `BabyBear .canonical` values; Montgomery
    realisations of a constant arise via the `to_mont` conversion op.
    `mont_mul` is the Montgomery-domain multiplication node, distinct from
    canonical `mul`; canonical `add`/`sub`/`neg` operate bit-identically on
    Montgomery-encoded values, so no separate Montgomery variants exist for
    those (one op, two valid interpretations selected by surrounding
    `to_mont`/`from_mont`). Shift ops are intentionally absent; they aren't
    field-level primitives and live in lowerings (REDC), not in the AST. -/
inductive ArithExpr where
  | const    : BabyBear .canonical → ArithExpr
  | var      : Nat → ArithExpr
  | add      : ArithExpr → ArithExpr → ArithExpr
  | sub      : ArithExpr → ArithExpr → ArithExpr
  | neg      : ArithExpr → ArithExpr
  | mul      : ArithExpr → ArithExpr → ArithExpr
  | montMul  : ArithExpr → ArithExpr → ArithExpr
  | toMont   : ArithExpr → ArithExpr
  | fromMont : ArithExpr → ArithExpr
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Number of AST nodes. -/
def ArithExpr.size : ArithExpr → Nat
  | .const _      => 1
  | .var _        => 1
  | .add a b      => 1 + a.size + b.size
  | .sub a b      => 1 + a.size + b.size
  | .neg a        => 1 + a.size
  | .mul a b      => 1 + a.size + b.size
  | .montMul a b  => 1 + a.size + b.size
  | .toMont a     => 1 + a.size
  | .fromMont a   => 1 + a.size

/-- Positional input arity: one more than the largest var index, or 0 if no
    vars. Computed pre-optimization so codegen preserves the source signature
    even when rules eliminate variable references (e.g. `a - a => 0`). -/
def ArithExpr.inputArity : ArithExpr → Nat
  | .const _      => 0
  | .var i        => i + 1
  | .add a b      => Nat.max a.inputArity b.inputArity
  | .sub a b      => Nat.max a.inputArity b.inputArity
  | .neg a        => a.inputArity
  | .mul a b      => Nat.max a.inputArity b.inputArity
  | .montMul a b  => Nat.max a.inputArity b.inputArity
  | .toMont a     => a.inputArity
  | .fromMont a   => a.inputArity

end TRZK
