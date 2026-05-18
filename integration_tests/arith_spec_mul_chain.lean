-- ArithExpr spec exercising a chain of three muls: x0 * (x1 * (x2 * x3)).
-- With the Montgomery-mixed rule set.
open TRZK (ArithExpr)

def spec : ArithExpr :=
  .mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))
