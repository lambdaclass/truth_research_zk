import TRZK.ArithExpr
import TRZK.Field.BabyBear

namespace TRZK

/-- Representation-tagged field value: the result type of evaluating an
    `ArithExpr`. The AST is representation-implicit while `BabyBear r` is
    representation-explicit, so the evaluator must carry which encoding a
    subtree produced for parent nodes to enforce operand-tag agreement. -/
inductive FieldVal where
  | canon : BabyBear .canonical → FieldVal
  | mont  : BabyBear .montgomery → FieldVal
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Denotational semantics of `ArithExpr` over BabyBear, total and
    structurally recursive so it can serve as a proof target.

    `add`/`sub`/`neg` are representation-polymorphic: they require matching
    operand tags and preserve the tag. `mul` is canonical-only; `montMul` is
    Montgomery-only; `toMont`/`fromMont` are the `·R` / `·R⁻¹` conversions.
    Representation-ill-typed trees (e.g. `montMul` on canonical operands)
    denote `none`. -/
def ArithExpr.eval (env : Nat → BabyBear .canonical) : ArithExpr → Option FieldVal
  | .const c     => some (.canon c)
  | .var i       => some (.canon (env i))
  | .add a b     =>
      match eval env a, eval env b with
      | some (.canon x), some (.canon y) => some (.canon (x + y))
      | some (.mont x),  some (.mont y)  => some (.mont (x + y))
      | _, _ => none
  | .sub a b     =>
      match eval env a, eval env b with
      | some (.canon x), some (.canon y) => some (.canon (x - y))
      | some (.mont x),  some (.mont y)  => some (.mont (x - y))
      | _, _ => none
  | .neg a       =>
      match eval env a with
      | some (.canon x) => some (.canon (-x))
      | some (.mont x)  => some (.mont (-x))
      | none => none
  | .mul a b     =>
      match eval env a, eval env b with
      | some (.canon x), some (.canon y) => some (.canon (x * y))
      | _, _ => none
  | .montMul a b =>
      match eval env a, eval env b with
      | some (.mont x), some (.mont y) => some (.mont (x.montMul y))
      | _, _ => none
  | .toMont a    =>
      match eval env a with
      | some (.canon x) => some (.mont x.toMont)
      | _ => none
  | .fromMont a  =>
      match eval env a with
      | some (.mont x) => some (.canon x.fromMont)
      | _ => none

end TRZK
