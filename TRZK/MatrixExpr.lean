import TRZK.ArithExpr

namespace TRZK

/-- 2D shape `(rows, cols)`. Concrete `Nat`s only (umbrella D7). -/
abbrev MatrixShape := Nat × Nat

/-- Matrix-layer AST. Minimal surface: enough for the matmul + transpose
    end-to-end pipeline. Additional ops (`hadamard`, `pointwise_scalar`,
    `reshape`, `permute`) arrive in the sub-changes whose harness exercises
    them.

    Constants store their dense element list in row-major order alongside
    the declared shape; well-formedness (entries.length = rows * cols) is
    checked by `MatrixExpr.shape`, which returns `none` for malformed
    nodes. -/
inductive MatrixExpr where
  | const_matrix : MatrixShape → List (BabyBear .canonical) → MatrixExpr
  | var_matrix   : Nat → MatrixShape → MatrixExpr
  | matmul       : MatrixExpr → MatrixExpr → MatrixExpr
  | transpose    : MatrixExpr → MatrixExpr
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Number of AST nodes. -/
def MatrixExpr.size : MatrixExpr → Nat
  | .const_matrix _ _ => 1
  | .var_matrix _ _   => 1
  | .matmul a b       => 1 + a.size + b.size
  | .transpose a      => 1 + a.size

/-- Derive the output shape of a matrix expression, returning `none` on any
    shape mismatch (malformed constant, matmul k-dim disagreement). -/
def MatrixExpr.shape : MatrixExpr → Option MatrixShape
  | .const_matrix (m, n) entries =>
      if entries.length = m * n then some (m, n) else none
  | .var_matrix _ s => some s
  | .matmul a b     => do
      let (m, k1) ← a.shape
      let (k2, n) ← b.shape
      if k1 = k2 then some (m, n) else none
  | .transpose a    => a.shape.map (fun (m, n) => (n, m))

end TRZK
