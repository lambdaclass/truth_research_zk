-- ArithExpr spec exercising a chain of three muls: x0 * (x1 * (x2 * x3)).
-- With the Montgomery-mixed rule set, cost-aware extraction prefers the
-- Montgomery realisation here (the canonical mul cost amortises across the
-- chain). The Rust output therefore uses bb_to_mont / bb_mont_mul /
-- bb_from_mont. Canonical-form inputs go in, canonical-form result comes
-- out, so the vectors are bit-identical to the canonical formulation.
open TRZK (ArithExpr)

def spec : ArithExpr :=
  .mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))
