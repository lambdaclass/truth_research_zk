import TRZK.Emit

open TRZK

#guard ArithExpr.inputArity (.add (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.add (.var 2) (.add (.var 0) (.var 2))) == 3
#guard ArithExpr.inputArity (.const 5) == 0
#guard ArithExpr.inputArity (.mul (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.mul (.var 2) (.mul (.var 0) (.var 2))) == 3
#guard ArithExpr.inputArity (.idiv (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.idiv (.var 0) (.const 1)) == 1
#guard ArithExpr.inputArity (.shl (.var 0) (.var 1)) == 2
#guard ArithExpr.inputArity (.shr (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.sub (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.sub (.var 2) (.sub (.var 0) (.var 2))) == 3
#guard ArithExpr.inputArity (.neg (.var 3)) == 4
#guard ArithExpr.inputArity (.neg (.neg (.var 0))) == 1
#guard ArithExpr.inputArity (.neg (.const 5)) == 0

#guard (ArithExpr.usedVars 3 (.add (.var 0) (.var 2))) == #[true, false, true]
#guard (ArithExpr.usedVars 2 (.const 5)) == #[false, false]
#guard (ArithExpr.usedVars 3 (.sub (.var 0) (.var 2))) == #[true, false, true]
#guard (ArithExpr.usedVars 2 (.neg (.var 1))) == #[false, true]
#guard (ArithExpr.usedVars 1 (.neg (.const 3))) == #[false]

private def emitArity (e : ArithExpr) : String :=
  emitFunction "arith_spec" e.inputArity e

#guard emitArity (.const 0) == "pub fn arith_spec() -> isize { 0isize }"
#guard emitArity (.var 0) == "pub fn arith_spec(x0: isize) -> isize { x0 }"
#guard emitArity (.add (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { x0.wrapping_add(x1) }"
#guard emitArity (.add (.var 0) (.const 0)) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_add(0isize) }"
#guard emitArity (.const (-5)) == "pub fn arith_spec() -> isize { (-5isize) }"
#guard emitArity (.add (.var 0) (.const (-1))) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_add((-1isize)) }"
#guard emitArity (.mul (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { x0.wrapping_mul(x1) }"
#guard emitArity (.mul (.var 0) (.const 1)) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_mul(1isize) }"
#guard emitArity (.mul (.var 0) (.const (-2))) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_mul((-2isize)) }"
#guard emitArity (.idiv (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { (x0 / x1) }"
#guard emitArity (.idiv (.var 0) (.const 1)) == "pub fn arith_spec(x0: isize) -> isize { (x0 / 1isize) }"
#guard emitArity (.idiv (.var 0) (.const (-2))) == "pub fn arith_spec(x0: isize) -> isize { (x0 / (-2isize)) }"
#guard emitArity (.shl (.var 0) (.const 0)) == "pub fn arith_spec(x0: isize) -> isize { x0.unbounded_shl(0isize as u32) }"
#guard emitArity (.shl (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { x0.unbounded_shl(x1 as u32) }"
#guard emitArity (.shr (.var 0) (.const 0)) == "pub fn arith_spec(x0: isize) -> isize { ((x0 as usize).unbounded_shr(0isize as u32) as isize) }"
#guard emitArity (.shr (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { ((x0 as usize).unbounded_shr(x1 as u32) as isize) }"

#guard emitArity (.sub (.var 0) (.var 1)) == "pub fn arith_spec(x0: isize, x1: isize) -> isize { x0.wrapping_sub(x1) }"
#guard emitArity (.sub (.var 0) (.const 3)) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_sub(3isize) }"
#guard emitArity (.sub (.var 0) (.const (-2))) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_sub((-2isize)) }"
#guard emitArity (.neg (.var 0)) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_neg() }"
#guard emitArity (.neg (.const 5)) == "pub fn arith_spec() -> isize { 5isize.wrapping_neg() }"
#guard emitArity (.neg (.const (-7))) == "pub fn arith_spec() -> isize { (-7isize).wrapping_neg() }"
#guard emitArity (.neg (.neg (.var 0))) == "pub fn arith_spec(x0: isize) -> isize { x0.wrapping_neg().wrapping_neg() }"

-- Arity preservation: caller passes a wider arity than the body uses
-- (simulating an opt that eliminated `var 1`); unused params get `_`.
#guard emitFunction "arith_spec" 2 (.var 0) == "pub fn arith_spec(x0: isize, _x1: isize) -> isize { x0 }"
#guard emitFunction "arith_spec" 3 (.const 0) == "pub fn arith_spec(_x0: isize, _x1: isize, _x2: isize) -> isize { 0isize }"
#guard emitFunction "arith_spec" 3 (.add (.var 0) (.var 2)) == "pub fn arith_spec(x0: isize, _x1: isize, x2: isize) -> isize { x0.wrapping_add(x2) }"
