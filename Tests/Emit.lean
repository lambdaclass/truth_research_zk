import TRZK.Emit

open TRZK

#guard ArithExpr.inputArity (.add (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.add (.var 2) (.add (.var 0) (.var 2))) == 3
#guard ArithExpr.inputArity (.const 5) == 0
#guard ArithExpr.inputArity (.mul (.var 1) (.var 0)) == 2
#guard ArithExpr.inputArity (.mul (.var 2) (.mul (.var 0) (.var 2))) == 3
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

private def emitBody (e : ArithExpr) : String := emitExpr e

#guard emitBody (.const 0) == "0u32"
#guard emitBody (.const 7) == "7u32"
#guard emitBody (.var 0) == "x0"
#guard emitBody (.add (.var 0) (.var 1)) == "bb_add(x0, x1)"
#guard emitBody (.add (.var 0) (.const 0)) == "bb_add(x0, 0u32)"
#guard emitBody (.mul (.var 0) (.var 1)) == "bb_mul(x0, x1)"
#guard emitBody (.mul (.var 0) (.const 1)) == "bb_mul(x0, 1u32)"
#guard emitBody (.sub (.var 0) (.var 1)) == "bb_sub(x0, x1)"
#guard emitBody (.sub (.var 0) (.const 3)) == "bb_sub(x0, 3u32)"
#guard emitBody (.neg (.var 0)) == "bb_neg(x0)"
#guard emitBody (.neg (.const 5)) == "bb_neg(5u32)"
#guard emitBody (.neg (.neg (.var 0))) == "bb_neg(bb_neg(x0))"

-- BabyBear field reduces literals into [0, p): -1 ≡ p-1.
#guard emitBody (.const (BabyBear.ofNat 0 - BabyBear.ofNat 1)) == s!"{BabyBear.p - 1}u32"

private def fnSig (arity : Nat) (e : ArithExpr) : String :=
  let body := emitFunction "arith_spec" arity e
  -- Strip the helper preamble so tests focus on the function signature/body.
  let helpersLen := emitHelpers.length
  body.drop (helpersLen + 1)

#guard fnSig 0 (.const 0) == "pub fn arith_spec() -> u32 { 0u32 }"
#guard fnSig 1 (.var 0) == "pub fn arith_spec(x0: u32) -> u32 { x0 }"
#guard fnSig 2 (.add (.var 0) (.var 1)) == "pub fn arith_spec(x0: u32, x1: u32) -> u32 { bb_add(x0, x1) }"

-- Arity preservation: caller passes a wider arity than the body uses; unused
-- params get `_`.
#guard fnSig 2 (.var 0) == "pub fn arith_spec(x0: u32, _x1: u32) -> u32 { x0 }"
#guard fnSig 3 (.const 0) == "pub fn arith_spec(_x0: u32, _x1: u32, _x2: u32) -> u32 { 0u32 }"
#guard fnSig 3 (.add (.var 0) (.var 2)) == "pub fn arith_spec(x0: u32, _x1: u32, x2: u32) -> u32 { bb_add(x0, x2) }"

-- The helper preamble is non-empty and starts with the modulus const.
#guard (emitHelpers.splitOn s!"const P: u32 = {BabyBear.p}u32;").length == 2

-- Montgomery / conversion ops lower to the runtime helpers.
#guard emitBody (.toMont (.var 0)) == "bb_to_mont(x0)"
#guard emitBody (.fromMont (.var 0)) == "bb_from_mont(x0)"
#guard emitBody (.montMul (.var 0) (.var 1)) == "bb_mont_mul(x0, x1)"
#guard
  emitBody (.fromMont (.montMul (.toMont (.var 0)) (.toMont (.var 1))))
    == "bb_from_mont(bb_mont_mul(bb_to_mont(x0), bb_to_mont(x1)))"

-- Helper preamble carries the Montgomery constants and core REDC routine.
#guard (emitHelpers.splitOn s!"const R: u32 = ").length == 2
#guard (emitHelpers.splitOn "const R_SQUARED: u32 = ").length == 2
#guard (emitHelpers.splitOn "const P_INV_NEG: u32 = ").length == 2
#guard (emitHelpers.splitOn "fn bb_redc(").length == 2
#guard (emitHelpers.splitOn "fn bb_to_mont(").length == 2
#guard (emitHelpers.splitOn "fn bb_from_mont(").length == 2
#guard (emitHelpers.splitOn "fn bb_mont_mul(").length == 2
