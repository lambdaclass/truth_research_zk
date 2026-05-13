import TRZK.ArithExpr

namespace TRZK

private def usedVarsAux (arity : Nat) : ArithExpr → Array Bool → Array Bool
  | .const _,     used => used
  | .var i,       used => if i < arity then used.set! i true else used
  | .add a b,     used => usedVarsAux arity b (usedVarsAux arity a used)
  | .sub a b,     used => usedVarsAux arity b (usedVarsAux arity a used)
  | .neg a,       used => usedVarsAux arity a used
  | .mul a b,     used => usedVarsAux arity b (usedVarsAux arity a used)
  | .montMul a b, used => usedVarsAux arity b (usedVarsAux arity a used)
  | .toMont a,    used => usedVarsAux arity a used
  | .fromMont a,  used => usedVarsAux arity a used

/-- Boolean array of length `arity`: `used[i]` is true iff `e` references
    `var i`. Vars with index ≥ arity are silently ignored (defensive: the
    contract is that callers pass `arity ≥ e.inputArity`). -/
def ArithExpr.usedVars (arity : Nat) (e : ArithExpr) : Array Bool :=
  usedVarsAux arity e (Array.replicate arity false)

/-- BabyBear modulus emitted as a Rust `u32` literal. -/
def emitModulus : String := s!"{BabyBear.p}u32"

/-- Montgomery radix `R = 2³² mod p` for BabyBear, emitted as a u32 literal.
    Computed at Lean elaboration time. -/
def emitR : String := s!"{BabyBear.toNat (⟨BabyBear.R⟩ : BabyBear .canonical)}u32"

/-- `R² mod p` for BabyBear, used to bootstrap `to_mont` via REDC. -/
def emitRsquared : String :=
  s!"{BabyBear.toNat (⟨BabyBear.R_squared⟩ : BabyBear .canonical)}u32"

/-- Helper functions injected at the top of every generated file.

    Canonical helpers (`bb_add`, `bb_sub`, `bb_neg`, `bb_mul`) implement the
    naive reduction from step 1. Montgomery helpers (`bb_redc`, `bb_to_mont`,
    `bb_from_mont`, `bb_mont_mul`) implement Montgomery arithmetic with
    `R = 2³² mod p`. `bb_mont_add`/`bb_mont_sub`/`bb_mont_neg` alias the
    canonical add/sub/neg because Montgomery encoding is linear (
    `x·R ± y·R = (x±y)·R`). Performance is intentionally not tuned. -/
def emitHelpers : String :=
  let lines : List String := [
    s!"#[allow(dead_code)] const P: u32 = {BabyBear.p}u32;",
    s!"#[allow(dead_code)] const P_U64: u64 = P as u64;",
    -- Montgomery radix R = 2^32 mod p; R² mod p for the to_mont bootstrap.
    s!"#[allow(dead_code)] const R: u32 = {emitR};",
    s!"#[allow(dead_code)] const R_SQUARED: u32 = {emitRsquared};",
    -- Modular inverse of -p mod 2^32, needed for REDC. Computed as
    -- `(P_U64.wrapping_neg() as u64).inv_mod_2_pow_32`; for BabyBear,
    -- p · p_inv ≡ -1 (mod 2^32), so p_inv = 2013265919 for p = 2^31 - 2^27 + 1.
    "#[allow(dead_code)] const P_INV_NEG: u32 = 2013265919u32;",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_add(a: u32, b: u32) -> u32 {",
    "    let s = (a as u64) + (b as u64);",
    "    if s >= P_U64 { (s - P_U64) as u32 } else { s as u32 }",
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
    "    (((a as u64) * (b as u64)) % P_U64) as u32",
    "}",
    "",
    -- REDC: given t < p·R, return t·R⁻¹ mod p in [0, p).
    "#[allow(dead_code)] #[inline]",
    "fn bb_redc(t: u64) -> u32 {",
    "    let m: u32 = (t as u32).wrapping_mul(P_INV_NEG);",
    "    let u: u64 = (t + (m as u64) * P_U64) >> 32;",
    "    let r: u32 = if u >= P_U64 { (u - P_U64) as u32 } else { u as u32 };",
    "    r",
    "}",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_to_mont(a: u32) -> u32 { bb_redc((a as u64) * (R_SQUARED as u64)) }",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_from_mont(a: u32) -> u32 { bb_redc(a as u64) }",
    "",
    "#[allow(dead_code)] #[inline]",
    "fn bb_mont_mul(a: u32, b: u32) -> u32 { bb_redc((a as u64) * (b as u64)) }",
    "",
    -- Montgomery add/sub/neg alias canonical: x·R ± y·R = (x±y)·R.
    "#[allow(dead_code)] #[inline] fn bb_mont_add(a: u32, b: u32) -> u32 { bb_add(a, b) }",
    "#[allow(dead_code)] #[inline] fn bb_mont_sub(a: u32, b: u32) -> u32 { bb_sub(a, b) }",
    "#[allow(dead_code)] #[inline] fn bb_mont_neg(a: u32) -> u32 { bb_neg(a) }",
    ""
  ]
  String.intercalate "\n" lines

/-- Emit a Rust `u32` BabyBear expression. Constants are reduced to their
    canonical residue `[0, p)` (already canonical via `BabyBear.toNat`); ops
    delegate to the helper functions emitted by `emitHelpers`. -/
def emitExpr : ArithExpr → String
  | .const n     => s!"{n.toNat}u32"
  | .var i       => s!"x{i}"
  | .add a b     => s!"bb_add({emitExpr a}, {emitExpr b})"
  | .sub a b     => s!"bb_sub({emitExpr a}, {emitExpr b})"
  | .neg a       => s!"bb_neg({emitExpr a})"
  | .mul a b     => s!"bb_mul({emitExpr a}, {emitExpr b})"
  | .montMul a b => s!"bb_mont_mul({emitExpr a}, {emitExpr b})"
  | .toMont a    => s!"bb_to_mont({emitExpr a})"
  | .fromMont a  => s!"bb_from_mont({emitExpr a})"

/-- Emit a full Rust function with a fixed positional arity: parameters are
    `x0..x(arity-1)` regardless of which survive optimization. Params not
    referenced by `e` get a leading `_` to silence Rust's unused-arg lint.
    Callers should pass the *pre-optimization* arity so the signature stays
    stable when rules eliminate variable references.

    The helper block (Montgomery and canonical helpers, modulus constant) is
    prepended so the generated file is self-contained. -/
def emitFunction (name : String) (arity : Nat) (e : ArithExpr) : String :=
  let used := e.usedVars arity
  let params := (List.range arity).map fun i =>
    if used.getD i false then s!"x{i}: u32" else s!"_x{i}: u32"
  let args := String.intercalate ", " params
  let body := emitExpr e
  s!"{emitHelpers}\npub fn {name}({args}) -> u32 \{ {body} }"

end TRZK
