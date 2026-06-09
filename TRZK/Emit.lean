import TRZK.ArithExpr
import TRZK.Program
import TRZK.LoopExpr

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

/-- Render a `ScalarType` as its Rust type name. -/
def emitScalarType : ScalarType → String
  | .u32 => "u32"

/-- Render a `RetTy` as its Rust return-type syntax. -/
def emitRetTy : RetTy → String
  | .scalar ty   => emitScalarType ty
  | .array ty n  => s!"[{emitScalarType ty}; {n}]"

/-- Emit a `ConstTable` as a top-level Rust `const NAME: [TY; N] = [...];`.
    Each value is rendered as a typed literal per `elemTy`. -/
def emitConstTable (t : ConstTable) : String :=
  let ty := emitScalarType t.elemTy
  let elems := String.intercalate ", " (t.values.toList.map fun v => s!"{v}{ty}")
  s!"const {t.name}: [{ty}; {t.values.size}] = [{elems}];"

/-- The set of body expressions a `FunctionBody` walks: a singleton for
    `.scalar`, one per cell for `.cells`. -/
def FunctionBody.exprs : FunctionBody → List ArithExpr
  | .scalar e  => [e]
  | .cells cs  => cs

/-- Emit a Rust function. Parameters are positional `x0..x(arity-1)` where
    `arity = f.params.length`; params not referenced by any body expression get
    a leading `_` to silence Rust's unused-arg lint. The signature stays stable
    even when optimization eliminates variable references because the arity is
    fixed by `params`. `isPub` controls the `pub` qualifier (entry vs. helper).

    `.scalar` bodies emit the expression directly; `.cells` bodies emit an
    array literal `[e0, e1, ...]`. -/
def emitFunction (isPub : Bool) (f : Function) : String :=
  let arity := f.params.length
  let exprs := f.body.exprs
  let used := exprs.foldl (fun acc e => (e.usedVars arity).zipWith (· || ·) acc)
                          (Array.replicate arity false)
  let params := (List.range arity).map fun i =>
    let (nm, ty) := f.params[i]!
    let pfx := if used.getD i false then "" else "_"
    s!"{pfx}{nm}: {emitScalarType ty}"
  let args := String.intercalate ", " params
  let body := match f.body with
    | .scalar e => emitExpr e
    | .cells cs => s!"[{String.intercalate ", " (cs.map emitExpr)}]"
  let qual := if isPub then "pub " else ""
  s!"{qual}fn {f.name}({args}) -> {emitRetTy f.retTy} \{ {body} }"

/-- Emit a full Rust file from a `Program`: the self-contained helper block,
    then each `ConstTable` as a top-level `const`, then private helper
    functions, then the public entry-point function. -/
def emitProgram (p : Program) : String :=
  let tables := p.tables.map emitConstTable
  let helpers := p.functions.map (emitFunction false ·)
  let entry := emitFunction true p.entry
  String.intercalate "\n" (emitHelpers :: tables ++ helpers ++ [entry])

/-! ## Loop IR emission

    `emitLoopProgram` is the matrix-path emitter: a tree-walk over `LoopExpr`
    (umbrella D1) producing a Rust function over a flat `mem` buffer, with the
    same positional-`x`-in / `[u32; N]`-out ABI the scalar path uses. -/

/-- Render an affine `IdxExpr` as a Rust `usize` expression. Loop variable `v`
    emits as `i{v}` (the loop counter the enclosing `for'` introduced). Rust's
    `+`/`*` precedence matches the affine algebra, so sums need no parens; only
    a scalar multiple of a sum is wrapped. -/
def emitIdx : IdxExpr → String
  | .const n          => s!"{n}"
  | .var v            => s!"i{v}"
  | .affine base s v  => if base == 0 then s!"{s} * i{v}" else s!"{base} + {s} * i{v}"
  | .add a b          => s!"{emitIdx a} + {emitIdx b}"
  | .mul c (.add a b) => s!"{c} * ({emitIdx (.add a b)})"
  | .mul c e          => s!"{c} * {emitIdx e}"

/-- Render a gather lane `(buffer, index)` as the Rust array read it stands
    for: `mem[idx]` or `TABLE[idx]`. -/
def emitGather : BufRef × IdxExpr → String
  | (.mem,        idx) => s!"mem[{emitIdx idx}]"
  | (.table name, idx) => s!"{name}[{emitIdx idx}]"

/-- Emit a `compute` kernel, resolving each `.var j` to gather lane `j`. The
    field ops reuse the canonical-domain helpers (`bb_add`, `bb_mul`, …), so a
    kernel built from `ArithExpr` emits identically to `emitExpr` except that
    its variables read through gathers. Out-of-range lanes (a malformed
    lowering) fall back to `0u32`. -/
def emitKernel (gathers : List (BufRef × IdxExpr)) : ArithExpr → String
  | .const n     => s!"{n.toNat}u32"
  | .var i       => match gathers[i]? with
                    | some g => emitGather g
                    | none   => "0u32"
  | .add a b     => s!"bb_add({emitKernel gathers a}, {emitKernel gathers b})"
  | .sub a b     => s!"bb_sub({emitKernel gathers a}, {emitKernel gathers b})"
  | .neg a       => s!"bb_neg({emitKernel gathers a})"
  | .mul a b     => s!"bb_mul({emitKernel gathers a}, {emitKernel gathers b})"
  | .montMul a b => s!"bb_mont_mul({emitKernel gathers a}, {emitKernel gathers b})"
  | .toMont a    => s!"bb_to_mont({emitKernel gathers a})"
  | .fromMont a  => s!"bb_from_mont({emitKernel gathers a})"

/-- Tree-walk emitter over `LoopExpr` (umbrella D1), one arm per constructor:
    - `for'` → a Rust `for i{idx} in {lo}..{hi} { … }` block, with
      `.step_by({step})` when `step ≠ 1` (the unit-stride case stays a bare
      range so the common output is unchanged);
    - `seq`  → the two bodies in order;
    - `compute` → `mem[scatter] {= | +=} kernel;` (accumulate selects `+=`);
    - `temp` → a `let mut mem` scratch-buffer declaration scoping the body;
    - `nop`  → nothing.
    `indent` is the current leading whitespace; nested blocks add four spaces. -/
partial def emitLoop (indent : String) : LoopExpr → String
  | .for' idx lo hi step body =>
    let inner := emitLoop (indent ++ "    ") body
    let range := if step == 1 then s!"{lo}..{hi}" else s!"({lo}..{hi}).step_by({step})"
    s!"{indent}for i{idx} in {range} \{\n{inner}\n{indent}}"
  | .seq a b =>
    s!"{emitLoop indent a}\n{emitLoop indent b}"
  | .compute kernel gathers scatter accumulate =>
    if accumulate then
      s!"{indent}mem[{emitIdx scatter}] = bb_add(mem[{emitIdx scatter}], {emitKernel gathers kernel});"
    else
      s!"{indent}mem[{emitIdx scatter}] = {emitKernel gathers kernel};"
  | .temp size body =>
    let inner := emitLoop (indent ++ "    ") body
    s!"{indent}\{\n{indent}    let mut mem: [u32; {size}] = [0u32; {size}];\n{inner}\n{indent}}"
  | .nop => ""

/-- Emit the full Rust file for a lowered matrix expression. Mirrors
    `emitProgram`'s shape — helper preamble, twiddle `const` tables, then the
    public entry function — but the entry body is the loop nest over `mem`.

    The entry seeds `mem[0..arity)` from the positional `x` parameters, runs
    `prog.body` (a `temp`-scoped loop nest), copies the result region
    `mem[outBase .. outBase + outSize)` into the returned `[u32; outSize]`, and
    returns it. The signature matches the scalar path's matrix arm, so the
    existing Rust harness links unchanged. -/
def emitLoopProgram (funcName : String) (prog : LoopProgram) : String :=
  let tables := prog.tables.map emitConstTable
  let params := String.intercalate ", "
    ((List.range prog.arity).map fun i => s!"x{i}: u32")
  -- The function body is itself the scratch-buffer scope, so the top-level
  -- `temp` adds no extra brace block — its size sizes `mem`, its inner nest is
  -- emitted at the body indent. Everything (buffer decl, input seeds, loop
  -- nest, result copy-out) sits at one 4-space level. `other` is the defensive
  -- path for a lowering that skipped the `temp` wrapper.
  let ind := "    "
  let memSize := match prog.body with | .temp size _ => size | _ => prog.memSize
  let inner := match prog.body with | .temp _ b => b | b => b
  let seeds := (List.range prog.arity).map fun i => s!"{ind}mem[{i}] = x{i};"
  let lines : List String :=
    [s!"{ind}let mut mem: [u32; {memSize}] = [0u32; {memSize}];"] ++
    seeds ++
    [emitLoop ind inner,
     s!"{ind}let mut out: [u32; {prog.outSize}] = [0u32; {prog.outSize}];",
     s!"{ind}for k in 0..{prog.outSize} \{ out[k] = mem[{prog.outBase} + k]; }",
     s!"{ind}out"]
  let bodyStr := String.intercalate "\n" lines
  let entry :=
    s!"pub fn {funcName}({params}) -> [u32; {prog.outSize}] \{\n{bodyStr}\n}"
  String.intercalate "\n" (emitHelpers :: tables ++ [entry])

end TRZK
