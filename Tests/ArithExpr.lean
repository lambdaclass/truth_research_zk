import TRZK.ArithExpr

open TRZK

#guard ArithExpr.size (.const 0) == 1
#guard ArithExpr.size (.var 5) == 1
#guard ArithExpr.size (.add (.var 0) (.const 0)) == 3
#guard ArithExpr.size (.add (.add (.var 0) (.var 1)) (.const 7)) == 5
#guard ArithExpr.size (.mul (.var 0) (.const 1)) == 3
#guard ArithExpr.size (.mul (.add (.var 0) (.var 1)) (.var 2)) == 5

#guard (ArithExpr.const 0 : ArithExpr) == .const 0
#guard (ArithExpr.add (.var 0) (.const 0)) != (.add (.const 0) (.var 0))
#guard (ArithExpr.mul (.var 0) (.const 1)) != (.mul (.const 1) (.var 0))
#guard (ArithExpr.mul (.var 0) (.var 1)) != (.add (.var 0) (.var 1))

#guard ArithExpr.size (.sub (.var 0) (.var 1)) == 3
#guard ArithExpr.size (.sub (.add (.var 0) (.var 1)) (.const 2)) == 5
#guard ArithExpr.size (.neg (.var 0)) == 2
#guard ArithExpr.size (.neg (.neg (.var 0))) == 3
#guard ArithExpr.size (.neg (.add (.var 0) (.var 1))) == 4
#guard (ArithExpr.sub (.var 0) (.var 1)) != (.sub (.var 1) (.var 0))
#guard (ArithExpr.sub (.var 0) (.var 1)) != (.add (.var 0) (.var 1))
#guard (ArithExpr.neg (.var 0)) != (.var 0)

-- BabyBear constants distinct from one another via field equality.
#guard (ArithExpr.const 0) != (.const 1)
#guard (ArithExpr.add (.var 0) (.const 7)) != (.add (.var 0) (.const 8))

-- Montgomery / conversion ops.
#guard ArithExpr.size (.toMont (.var 0)) == 2
#guard ArithExpr.size (.fromMont (.var 0)) == 2
#guard ArithExpr.size (.montMul (.var 0) (.var 1)) == 3
#guard ArithExpr.size (.fromMont (.montMul (.toMont (.var 0)) (.toMont (.var 1)))) == 6

#guard (ArithExpr.toMont (.var 0)) != (.fromMont (.var 0))
#guard (ArithExpr.mul (.var 0) (.var 1)) != (.montMul (.var 0) (.var 1))

-- Arity passes through conversion ops unchanged.
#guard ArithExpr.inputArity (.toMont (.var 3)) == 4
#guard ArithExpr.inputArity (.fromMont (.var 3)) == 4
#guard ArithExpr.inputArity (.montMul (.var 0) (.var 2)) == 3
