import TRZK.MatrixExpr
import TRZK.MatrixLower
import TRZK.MatrixPipeline

open TRZK

/-! Tests for the NTT/iNTT matrix-layer primitives. -/

namespace TestNtt

/-- BabyBear modulus, mirrored for test computations. -/
private def P : Nat := BabyBear.p

/-- Tiny tree evaluator over the canonical residue range. Structural; the
    real codegen lowering lives in `TRZK.Emit`. -/
private partial def eval (env : Nat → Nat) : ArithExpr → Nat
  | .const c     => c.toNat
  | .var i       => env i
  | .add a b     => (eval env a + eval env b) % P
  | .sub a b     =>
      let av := eval env a
      let bv := eval env b
      (av + (P - bv % P)) % P
  | .neg a       => (P - eval env a % P) % P
  | .mul a b     => (eval env a * eval env b) % P
  | .montMul a b => (eval env a * eval env b) % P
  | .toMont a    => eval env a
  | .fromMont a  => eval env a

private def envOf (xs : List Nat) : Nat → Nat
  | i => xs.toArray[i]?.getD 0

/-- A known multiplicative generator of `(Z/p)*` for BabyBear. -/
private def gGen : BabyBear .canonical := ⟨31⟩

/-- Fast exponentiation in `BabyBear .canonical`: square-and-multiply on
    the binary representation of `k`. Required for the `(p-1)/n` exponents
    used to derive primitive roots, which exceed 2³⁰ for small `n`. -/
private partial def bbPow (a : BabyBear .canonical) (k : Nat) : BabyBear .canonical :=
  if k = 0 then ⟨1⟩
  else
    let half := bbPow a (k / 2)
    let sq := half * half
    if k % 2 = 0 then sq else sq * a

/-- Primitive `n`-th root of unity: `g^((p-1)/n) mod p`. Requires `n ∣ (p-1)`;
    callers in this file pick `n` a power of two with `n ≤ 2^27`. -/
private def omega (n : Nat) : BabyBear .canonical :=
  bbPow gGen ((P - 1) / n)

end TestNtt

open TestNtt

/-! Smart-constructor preconditions. -/

-- Valid sizes accepted: n = 1, 2, 4, 8, 16, ..., 2^27.
#guard (MatrixExpr.mkNtt 8 (omega 8) (.var_matrix 0 (1, 8))).isSome
#guard (MatrixExpr.mkIntt 16 (omega 16) (.var_matrix 0 (1, 16))).isSome

-- Non-power-of-two rejected.
#guard (MatrixExpr.mkNtt 6 (omega 8) (.var_matrix 0 (1, 6))).isNone
-- 2^28 exceeds the 2-adic valuation 27 of p - 1.
#guard (MatrixExpr.mkNtt (2 ^ 28) (omega 8) (.var_matrix 0 (1, 2 ^ 28))).isNone

-- Shape mismatch rejected: wrong column count.
#guard (MatrixExpr.mkNtt 8 (omega 8) (.var_matrix 0 (1, 4))).isNone
-- Shape mismatch rejected: not a row vector.
#guard (MatrixExpr.mkNtt 8 (omega 8) (.var_matrix 0 (2, 8))).isNone

/-! Shape derivation. -/

#guard MatrixExpr.shape (.ntt 8 (omega 8) (.var_matrix 0 (1, 8))) == some (1, 8)
#guard MatrixExpr.shape (.intt 8 (omega 8) (.var_matrix 0 (1, 8))) == some (1, 8)
#guard MatrixExpr.shape (.ntt 8 (omega 8) (.var_matrix 0 (1, 7))) == none

/-! AST size. -/

#guard MatrixExpr.size (.ntt 8 (omega 8) (.var_matrix 0 (1, 8))) == 2

/-! Lowering: NTT followed by iNTT round-trips at n = 4. The matrix
    pipeline rewrite is not invoked here; we materialize directly and
    evaluate per cell, which exercises the lowered scalar program.

    Pick a small `n` so the unrolled DFT stays cheap. The omega for n=4
    over BabyBear is `g^((p-1)/4)`. -/

private def vec4 : List Nat := [3, 5, 7, 11]

-- Forward then inverse of a length-4 vector returns the original.
#guard
  let ω := omega 4
  let inp : MatrixExpr := .var_matrix 0 (1, 4)
  let nttExpr : MatrixExpr := .intt 4 ω (.ntt 4 ω inp)
  match nttExpr.materialize with
  | some (grid, _) =>
      grid.size == 1 &&
      grid[0]!.size == 4 &&
      (List.range 4).all (fun k =>
        eval (envOf vec4) grid[0]![k]! == vec4.toArray[k]!)
  | none => false

-- Forward then inverse of a length-8 vector returns the original.
private def vec8 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]

#guard
  let ω := omega 8
  let inp : MatrixExpr := .var_matrix 0 (1, 8)
  let nttExpr : MatrixExpr := .intt 8 ω (.ntt 8 ω inp)
  match nttExpr.materialize with
  | some (grid, _) =>
      grid.size == 1 &&
      grid[0]!.size == 8 &&
      (List.range 8).all (fun k =>
        eval (envOf vec8) grid[0]![k]! == vec8.toArray[k]!)
  | none => false

/-! Rewrite rule: `intt n ω (ntt n ω x) → x` collapses during saturation.
    The composed expression saturates to plain `var_matrix 0`. -/

#guard
  let ω := omega 4
  let inp : MatrixExpr := .var_matrix 0 (1, 4)
  let spec : MatrixExpr := .intt 4 ω (.ntt 4 ω inp)
  let rules := MatrixRuleSet.default.withNttRoundTrip 4 ω
  match MatrixPipeline.optimize rules spec with
  | some result => result == inp
  | none => false

-- And the other direction: `ntt n ω (intt n ω x) → x`.
#guard
  let ω := omega 4
  let inp : MatrixExpr := .var_matrix 0 (1, 4)
  let spec : MatrixExpr := .ntt 4 ω (.intt 4 ω inp)
  let rules := MatrixRuleSet.default.withNttRoundTrip 4 ω
  match MatrixPipeline.optimize rules spec with
  | some result => result == inp
  | none => false

-- The rule is `(n, ω)`-specific: a different `n` does not collapse.
#guard
  let ω4 := omega 4
  let ω8 := omega 8
  let inp : MatrixExpr := .var_matrix 0 (1, 4)
  let spec : MatrixExpr := .intt 4 ω4 (.ntt 4 ω4 inp)
  -- Provide round-trip rules only for n = 8; nothing should fire.
  let rules := MatrixRuleSet.default.withNttRoundTrip 8 ω8
  match MatrixPipeline.optimize rules spec with
  | some result => result == spec
  | none => false
