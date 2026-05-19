-- ArithExpr spec exercising the new field rule `add_neg_self`: x + (-x) → 0.
-- The optimizer reduces this to the constant 0; codegen still emits a 1-ary
-- function so the caller interface stays stable.
open TRZK (ArithExpr)

def spec : ArithExpr := .add (.var 0) (.neg (.var 0))
