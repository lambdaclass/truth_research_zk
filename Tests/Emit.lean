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

private def mkParams (arity : Nat) : List (String × ScalarType) :=
  (List.range arity).map fun i => (s!"x{i}", ScalarType.u32)

/-- Wrap a scalar body as a trivial `Program` (no tables, no helpers) and emit
    just the entry function, stripping the helper preamble. -/
private def fnSig (arity : Nat) (e : ArithExpr) : String :=
  let prog : Program :=
    { tables := [], functions := [],
      entry := { name := "arith_spec", params := mkParams arity,
                 retTy := .scalar .u32, body := .scalar e } }
  let code := emitProgram prog
  code.drop (emitHelpers.length + 1)

#guard fnSig 0 (.const 0) == "pub fn arith_spec() -> u32 { 0u32 }"
#guard fnSig 1 (.var 0) == "pub fn arith_spec(x0: u32) -> u32 { x0 }"
#guard fnSig 2 (.add (.var 0) (.var 1)) == "pub fn arith_spec(x0: u32, x1: u32) -> u32 { bb_add(x0, x1) }"

-- Arity preservation: caller passes a wider arity than the body uses; unused
-- params get `_`.
#guard fnSig 2 (.var 0) == "pub fn arith_spec(x0: u32, _x1: u32) -> u32 { x0 }"
#guard fnSig 3 (.const 0) == "pub fn arith_spec(_x0: u32, _x1: u32, _x2: u32) -> u32 { 0u32 }"
#guard fnSig 3 (.add (.var 0) (.var 2)) == "pub fn arith_spec(x0: u32, _x1: u32, x2: u32) -> u32 { bb_add(x0, x2) }"

-- Matrix (`.cells`) body: emits an array literal and an `[u32; N]` return type.
-- Unused params get `_` when no cell references them.
private def cellSig (arity : Nat) (cells : List ArithExpr) : String :=
  let prog : Program :=
    { tables := [], functions := [],
      entry := { name := "arith_spec", params := mkParams arity,
                 retTy := .array .u32 cells.length, body := .cells cells } }
  (emitProgram prog).drop (emitHelpers.length + 1)

#guard cellSig 2 [.var 0, .var 1] ==
  "pub fn arith_spec(x0: u32, x1: u32) -> [u32; 2] { [x0, x1] }"
#guard cellSig 2 [.add (.var 0) (.var 1)] ==
  "pub fn arith_spec(x0: u32, x1: u32) -> [u32; 1] { [bb_add(x0, x1)] }"
-- x1 is unused across all cells -> prefixed.
#guard cellSig 2 [.var 0, .var 0] ==
  "pub fn arith_spec(x0: u32, _x1: u32) -> [u32; 2] { [x0, x0] }"

-- ConstTable emits as a top-level Rust const array.
#guard emitConstTable { name := "_t", elemTy := .u32, values := #[1, 2, 3] } ==
  "const _t: [u32; 3] = [1u32, 2u32, 3u32];"
#guard emitConstTable { name := "_e", elemTy := .u32, values := #[] } ==
  "const _e: [u32; 0] = [];"

-- A Program with tables and a private helper: helper has no `pub`, the table
-- emits at the top (after helpers), and the entry is the only `pub fn`.
private def progWithHelpers : Program :=
  { tables := [{ name := "_twiddles_4", elemTy := .u32, values := #[1, 0, 1, 0] }],
    functions := [{ name := "_helper", params := [("x0", .u32)],
                    retTy := .scalar .u32, body := .scalar (.var 0) }],
    entry := { name := "arith_spec", params := [("x0", .u32)],
               retTy := .scalar .u32, body := .scalar (.var 0) } }

#guard ((emitProgram progWithHelpers).splitOn "const _twiddles_4: [u32; 4] = [1u32, 0u32, 1u32, 0u32];").length == 2
#guard ((emitProgram progWithHelpers).splitOn "fn _helper(x0: u32) -> u32 { x0 }").length == 2
-- exactly one `pub fn` in the file (the entry); the helper carries none.
#guard ((emitProgram progWithHelpers).splitOn "pub fn ").length == 2
#guard ((emitProgram progWithHelpers).splitOn "pub fn arith_spec(x0: u32) -> u32 { x0 }").length == 2

-- Construction and equality on representative shapes (task 1.4).
#guard (({ tables := [], functions := [],
           entry := { name := "arith_spec", params := [], retTy := .scalar .u32,
                      body := .scalar (.const 0) } } : Program) ==
        { tables := [], functions := [],
          entry := { name := "arith_spec", params := [], retTy := .scalar .u32,
                     body := .scalar (.const 0) } }) == true
#guard (({ tables := [], functions := [],
           entry := { name := "arith_spec", params := [], retTy := .scalar .u32,
                      body := .scalar (.const 0) } } : Program) ==
        { tables := [], functions := [],
          entry := { name := "arith_spec", params := [], retTy := .scalar .u32,
                     body := .scalar (.const 1) } }) == false
#guard (RetTy.array .u32 8 == RetTy.array .u32 8) == true
#guard (RetTy.array .u32 8 == RetTy.array .u32 4) == false
#guard (RetTy.scalar .u32 == RetTy.array .u32 1) == false

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
