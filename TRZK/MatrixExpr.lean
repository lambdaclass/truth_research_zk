import TRZK.ArithExpr

namespace TRZK

/-- 2D shape `(rows, cols)`. Concrete `Nat`s only (umbrella D7). -/
abbrev MatrixShape := Nat × Nat

/-- Matrix-layer AST. Minimal surface: enough for the matmul + transpose
    end-to-end pipeline plus NTT/iNTT primitives. Additional ops
    (`hadamard`, `pointwise_scalar`, `reshape`, `permute`) arrive in the
    sub-changes whose harness exercises them.

    Constants store their dense element list in row-major order alongside
    the declared shape; well-formedness (entries.length = rows * cols) is
    checked by `MatrixExpr.shape`, which returns `none` for malformed
    nodes.

    `ntt`/`intt` carry their length `n` and primitive `n`-th root of unity
    `ω`; the input is a length-`n` row vector (a `1 × n` matrix). The
    precondition `n` power of two and `n ∣ p − 1` is discharged by the
    smart constructors `MatrixExpr.ntt`/`MatrixExpr.intt` below, so any raw
    `.ntt`/`.intt` node in scope already satisfies it. -/
inductive MatrixExpr where
  | const_matrix : MatrixShape → List (BabyBear .canonical) → MatrixExpr
  | var_matrix   : Nat → MatrixShape → MatrixExpr
  | matmul       : MatrixExpr → MatrixExpr → MatrixExpr
  | transpose    : MatrixExpr → MatrixExpr
  | ntt          : Nat → BabyBear .canonical → MatrixExpr → MatrixExpr
  | intt         : Nat → BabyBear .canonical → MatrixExpr → MatrixExpr
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Number of AST nodes. -/
def MatrixExpr.size : MatrixExpr → Nat
  | .const_matrix _ _ => 1
  | .var_matrix _ _   => 1
  | .matmul a b       => 1 + a.size + b.size
  | .transpose a      => 1 + a.size
  | .ntt _ _ a        => 1 + a.size
  | .intt _ _ a       => 1 + a.size

/-- Derive the output shape of a matrix expression, returning `none` on any
    shape mismatch (malformed constant, matmul k-dim disagreement, NTT
    applied to a non-`1 × n` shape). -/
def MatrixExpr.shape : MatrixExpr → Option MatrixShape
  | .const_matrix (m, n) entries =>
      if entries.length = m * n then some (m, n) else none
  | .var_matrix _ s => some s
  | .matmul a b     => do
      let (m, k1) ← a.shape
      let (k2, n) ← b.shape
      if k1 = k2 then some (m, n) else none
  | .transpose a    => a.shape.map (fun (m, n) => (n, m))
  | .ntt n _ a      => do
      let (rows, cols) ← a.shape
      if rows = 1 ∧ cols = n then some (1, n) else none
  | .intt n _ a     => do
      let (rows, cols) ← a.shape
      if rows = 1 ∧ cols = n then some (1, n) else none

/-- Smart constructor for the forward NTT primitive. Returns `none` if `n`
    is not a valid BabyBear NTT size (power of two, `n ∣ p − 1`) or if `x`
    is not a `1 × n` row vector. -/
def MatrixExpr.mkNtt (n : Nat) (ω : BabyBear .canonical) (x : MatrixExpr) :
    Option MatrixExpr := do
  guard (BabyBear.isNttSize n)
  let (rows, cols) ← x.shape
  guard (rows = 1 ∧ cols = n)
  some (.ntt n ω x)

/-- Smart constructor for the inverse NTT primitive. Same preconditions as
    `mkNtt`. -/
def MatrixExpr.mkIntt (n : Nat) (ω : BabyBear .canonical) (x : MatrixExpr) :
    Option MatrixExpr := do
  guard (BabyBear.isNttSize n)
  let (rows, cols) ← x.shape
  guard (rows = 1 ∧ cols = n)
  some (.intt n ω x)

end TRZK
