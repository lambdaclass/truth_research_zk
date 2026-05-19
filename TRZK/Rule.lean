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

/-- The list of rewrite rules `Pipeline.optimize` consumes. -/
abbrev RuleSet := List (RewriteRule ArithOp)

/-- BabyBear rule set in the naive representation. -/
def RuleSet.babybearNaive : RuleSet :=
  [addZeroRight, addNegSelf, mulOneRight, mulZeroRight, subSelfZero, negNeg]

end TRZK
