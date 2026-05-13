import TRZK.ArithOp

open LambdaSat

namespace TRZK

/-- Right-identity of `Add`: `e + 0 → e`. -/
def addZeroRight : RewriteRule ArithOp where
  name := "add_zero_right"
  lhs := .node (.add 0 0) [.patVar 0, .node (.const 0) []]
  rhs := .patVar 0

/-- Additive inverse: `x + (−x) → 0`. -/
def addNegSelf : RewriteRule ArithOp where
  name := "add_neg_self"
  lhs := .node (.add 0 0) [.patVar 0, .node (.neg 0) [.patVar 0]]
  rhs := .node (.const 0) []

/-- Right-identity of `Mul`: `e * 1 → e`. -/
def mulOneRight : RewriteRule ArithOp where
  name := "mul_one_right"
  lhs := .node (.mul 0 0) [.patVar 0, .node (.const 1) []]
  rhs := .patVar 0

/-- Right-zero of `Mul`: `e * 0 → 0`. The optimized form drops `e` entirely;
    callers must preserve the original input arity through codegen. -/
def mulZeroRight : RewriteRule ArithOp where
  name := "mul_zero_right"
  lhs := .node (.mul 0 0) [.patVar 0, .node (.const 0) []]
  rhs := .node (.const 0) []

/-- Self-subtraction: `x - x → 0`. -/
def subSelfZero : RewriteRule ArithOp where
  name := "sub_self_zero"
  lhs := .node (.sub 0 0) [.patVar 0, .patVar 0]
  rhs := .node (.const 0) []

/-- Double negation elimination: `-(-x) → x`. -/
def negNeg : RewriteRule ArithOp where
  name := "neg_neg"
  lhs := .node (.neg 0) [.node (.neg 0) [.patVar 0]]
  rhs := .patVar 0

/-- Conversion round-trip: `to_mont (from_mont e) → e` for any subexpression
    `e` (matched by `patVar 0`). Sound because `to_mont (from_mont e) =
    e · R⁻¹ · R = e` in `ZMod p`. -/
def toFromMont : RewriteRule ArithOp where
  name := "to_from_mont"
  lhs := .node (.toMont 0) [.node (.fromMont 0) [.patVar 0]]
  rhs := .patVar 0

/-- Conversion round-trip in the other direction: `from_mont (to_mont e) → e`. -/
def fromToMont : RewriteRule ArithOp where
  name := "from_to_mont"
  lhs := .node (.fromMont 0) [.node (.toMont 0) [.patVar 0]]
  rhs := .patVar 0

/-- Cross-repr lowering for multiplication. Directed: the egraph introduces
    the Montgomery form when it sees a canonical mul; the round-trip rules
    collapse any redundant conversions on either side.

    `mul a b → from_mont (mont_mul (to_mont a) (to_mont b))`

    Cost-aware extraction decides whether the Montgomery realisation wins
    for the surrounding context: chained muls amortise the conversion cost;
    single muls keep canonical. -/
def mulCrossRepr : RewriteRule ArithOp where
  name := "mul_cross_repr"
  lhs := .node (.mul 0 0) [.patVar 0, .patVar 1]
  rhs :=
    .node (.fromMont 0)
      [.node (.montMul 0 0)
        [.node (.toMont 0) [.patVar 0],
         .node (.toMont 0) [.patVar 1]]]

/-- Trivial constant fold: `to_mont 0 → 0`. Sound because `0 · R = 0`.
    Non-trivial cases (`to_mont (.const c) → .const (c·R mod p)` for
    arbitrary `c`) need computed-RHS rule support the engine does not
    currently provide. -/
def toMontZero : RewriteRule ArithOp where
  name := "to_mont_zero"
  lhs := .node (.toMont 0) [.node (.const 0) []]
  rhs := .node (.const 0) []

/-- Trivial constant fold: `from_mont 0 → 0`. Sound because `0 · R⁻¹ = 0`. -/
def fromMontZero : RewriteRule ArithOp where
  name := "from_mont_zero"
  lhs := .node (.fromMont 0) [.node (.const 0) []]
  rhs := .node (.const 0) []

/-- The list of rewrite rules `Pipeline.optimize` consumes. -/
abbrev RuleSet := List (RewriteRule ArithOp)

/-- BabyBear rule set in the naive (canonical-only) representation. -/
def RuleSet.babybearNaive : RuleSet :=
  [addZeroRight, addNegSelf, mulOneRight, mulZeroRight, subSelfZero, negNeg]

/-- BabyBear rule set extended with Montgomery-mixed rewrites. Inherits the
    canonical-only rules and adds the conversion round-trip rules, the
    cross-repr mul lowering, and trivial Montgomery constant folds. -/
def RuleSet.babybearMixed : RuleSet :=
  RuleSet.babybearNaive ++
    [toFromMont, fromToMont, mulCrossRepr, toMontZero, fromMontZero]

end TRZK
