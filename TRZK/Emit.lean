import TRZK.ArithExpr

namespace TRZK

private def usedVarsAux (arity : Nat) : ArithExpr → Array Bool → Array Bool
  | .const _, used => used
  | .var i,   used => if i < arity then used.set! i true else used
  | .add a b, used => usedVarsAux arity b (usedVarsAux arity a used)
  | .sub a b, used => usedVarsAux arity b (usedVarsAux arity a used)
  | .neg a,   used => usedVarsAux arity a used
  | .mul a b, used => usedVarsAux arity b (usedVarsAux arity a used)

/-- Boolean array of length `arity`: `used[i]` is true iff `e` references
    `var i`. Vars with index ≥ arity are silently ignored (defensive: the
    contract is that callers pass `arity ≥ e.inputArity`). -/
def ArithExpr.usedVars (arity : Nat) (e : ArithExpr) : Array Bool :=
  usedVarsAux arity e (Array.replicate arity false)

/-- BabyBear modulus emitted as a Rust `u32` literal. -/
def emitModulus : String := s!"{BabyBear.p}u32"

/-- Helper functions injected at the top of every generated file.
    Naive canonical reduction: u32 params, u64 intermediates, branchless or
    conditional reduction back into `[0, p)`. Performance is step 2's problem. -/
def emitHelpers : String :=
  let lines : List String := [
    s!"#[allow(dead_code)] const P: u32 = {BabyBear.p}u32;",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_add(a: u32, b: u32) -> u32 {",
    "    let s = (a as u64) + (b as u64);",
    "    if s >= P as u64 { (s - P as u64) as u32 } else { s as u32 }",
    "}",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_sub(a: u32, b: u32) -> u32 {",
    "    if a >= b { a - b } else { a + (P - b) }",
    "}",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_neg(a: u32) -> u32 {",
    "    if a == 0 { 0 } else { P - a }",
    "}",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_mul(a: u32, b: u32) -> u32 {",
    "    (((a as u64) * (b as u64)) % (P as u64)) as u32",
    "}",
    ""
  ]
  String.intercalate "\n" lines

/-- Emit a Rust `u32` BabyBear expression. Constants are reduced to their
    canonical residue `[0, p)` (already canonical via `BabyBear.toNat`); ops
    delegate to the helper functions emitted by `emitHelpers`. -/
def emitExpr : ArithExpr → String
  | .const n => s!"{n.toNat}u32"
  | .var i   => s!"x{i}"
  | .add a b => s!"bb_add({emitExpr a}, {emitExpr b})"
  | .sub a b => s!"bb_sub({emitExpr a}, {emitExpr b})"
  | .neg a   => s!"bb_neg({emitExpr a})"
  | .mul a b => s!"bb_mul({emitExpr a}, {emitExpr b})"

/-- Emit a full Rust function with a fixed positional arity: parameters are
    `x0..x(arity-1)` regardless of which survive optimization. Params not
    referenced by `e` get a leading `_` to silence Rust's unused-arg lint.
    Callers should pass the *pre-optimization* arity so the signature stays
    stable when rules eliminate variable references.

    The helper block (`bb_add`, `bb_sub`, `bb_neg`, `bb_mul`, `P`) is prepended
    so the generated file is self-contained. -/
def emitFunction (name : String) (arity : Nat) (e : ArithExpr) : String :=
  let used := e.usedVars arity
  let params := (List.range arity).map fun i =>
    if used.getD i false then s!"x{i}: u32" else s!"_x{i}: u32"
  let args := String.intercalate ", " params
  let body := emitExpr e
  s!"{emitHelpers}\npub fn {name}({args}) -> u32 \{ {body} }"

end TRZK
