import TRZK.Pipeline

open TRZK

#guard optimize RuleSet.babybearNaive (.add (.var 0) (.const 0)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.add (.var 5) (.const 0)) == some (.var 5)
#guard optimize RuleSet.babybearNaive (.add (.const 0) (.var 0)) == some (.add (.const 0) (.var 0))
#guard optimize RuleSet.babybearNaive (.add (.add (.var 0) (.const 0)) (.const 0)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.add (.var 0) (.const 7)) == some (.add (.var 0) (.const 7))
#guard optimize RuleSet.babybearNaive (.const 0) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.var 3) == some (.var 3)

#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 5) (.const 1)) == some (.var 5)
#guard optimize RuleSet.babybearNaive (.mul (.const 1) (.var 0)) == some (.mul (.const 1) (.var 0))
#guard optimize RuleSet.babybearNaive (.mul (.mul (.var 0) (.const 1)) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.const 7)) == some (.mul (.var 0) (.const 7))
#guard optimize RuleSet.babybearNaive (.mul (.add (.var 0) (.const 0)) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.var 1)) == some (.mul (.var 0) (.var 1))

#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.const 0)) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 5) (.const 0)) == some (.const 0)

#guard optimize RuleSet.babybearNaive (.sub (.var 0) (.var 0)) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.sub (.var 5) (.var 5)) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.sub (.var 0) (.var 1)) == some (.sub (.var 0) (.var 1))
#guard optimize RuleSet.babybearNaive (.add (.sub (.var 0) (.var 0)) (.const 0)) == some (.const 0)

#guard optimize RuleSet.babybearNaive (.neg (.neg (.var 0))) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.neg (.neg (.var 5))) == some (.var 5)
#guard optimize RuleSet.babybearNaive (.neg (.neg (.neg (.neg (.var 0))))) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.neg (.var 0)) == some (.neg (.var 0))

-- New rule: x + (-x) → 0.
#guard optimize RuleSet.babybearNaive (.add (.var 0) (.neg (.var 0))) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.add (.var 5) (.neg (.var 5))) == some (.const 0)

-- Montgomery / mixed rule set --------------------------------------------------

-- Conversion round-trips collapse in either direction.
#guard optimize RuleSet.babybearMixed (.toMont (.fromMont (.var 0))) == some (.var 0)
#guard optimize RuleSet.babybearMixed (.fromMont (.toMont (.var 0))) == some (.var 0)

-- Round-trip cancels even when the inner subexpression is a non-trivial tree.
#guard
  optimize RuleSet.babybearMixed (.fromMont (.toMont (.add (.var 0) (.var 1))))
    == some (.add (.var 0) (.var 1))

-- Trivial Montgomery constant folds.
#guard optimize RuleSet.babybearMixed (.toMont (.const 0)) == some (.const 0)
#guard optimize RuleSet.babybearMixed (.fromMont (.const 0)) == some (.const 0)

-- All canonical-only optimisations still apply with the mixed rule set.
#guard optimize RuleSet.babybearMixed (.add (.var 0) (.const 0)) == some (.var 0)
#guard optimize RuleSet.babybearMixed (.mul (.var 0) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearMixed (.sub (.var 0) (.var 0)) == some (.const 0)
#guard optimize RuleSet.babybearMixed (.neg (.neg (.var 0))) == some (.var 0)

-- A single canonical mul stays canonical: the cross-repr rewrite introduces a
-- Montgomery realisation in the e-graph, but cost-aware extraction picks the
-- cheaper canonical form (mul=8 vs to_mont+mont_mul+to_mont+from_mont=13).
#guard optimize RuleSet.babybearMixed (.mul (.var 0) (.var 1)) == some (.mul (.var 0) (.var 1))

-- A chain of three muls prefers the Montgomery realisation. The extracted
-- form is `from_mont(mont_mul(to_mont a, mont_mul(to_mont b, mont_mul(to_mont c, to_mont d))))`,
-- a chain of mont_muls bracketed by one from_mont and four to_monts.
-- Canonical cost: 3*8 = 24. Montgomery cost: 4 + 3*1 + 4*4 = 23.
private def chainExpr : ArithExpr :=
  .mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))
private def chainMont : ArithExpr :=
  .fromMont
    (.montMul (.toMont (.var 0))
      (.montMul (.toMont (.var 1))
        (.montMul (.toMont (.var 2)) (.toMont (.var 3)))))
#guard optimize RuleSet.babybearMixed chainExpr == some chainMont
