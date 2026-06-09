import TRZK.MatrixLower

open TRZK

/-! Tests for the matrix-to-scalar unrolling. -/

namespace TestEval

/-- Tiny tree evaluator over `Nat` mod BabyBear, just for these tests.
    Real codegen lowering lives in `TRZK.Emit`; this is structural only. -/
private partial def eval (env : Nat → Nat) : ArithExpr → Nat
  | .const n     => n.toNat
  | .var i       => env i
  | .add a b     => (eval env a + eval env b) % BabyBear.p
  | .sub a b     =>
      let av := eval env a
      let bv := eval env b
      (av + (BabyBear.p - bv % BabyBear.p)) % BabyBear.p
  | .neg a       =>
      let av := eval env a
      (BabyBear.p - av % BabyBear.p) % BabyBear.p
  | .mul a b     => (eval env a * eval env b) % BabyBear.p
  | .montMul a b => (eval env a * eval env b) % BabyBear.p -- unused here
  | .toMont a    => eval env a -- unused here
  | .fromMont a  => eval env a -- unused here

end TestEval

/-- Lookup helper for unrolled tests. -/
private def envOf (xs : List Nat) : Nat → Nat
  | i => xs.toArray[i]?.getD 0

/-! Arity allocation. -/

-- Single var_matrix allocates m·n inputs.
#guard
  match (MatrixExpr.var_matrix 0 (2, 3)).materialize with
  | some (_, arity) => arity == 6
  | none => false

-- Same var_matrix used twice shares the base.
#guard
  match (MatrixExpr.matmul (.transpose (.var_matrix 0 (2, 3)))
                           (.var_matrix 0 (2, 3))).materialize with
  | some (_, arity) => arity == 6
  | none => false

-- Distinct var_matrix indices allocate distinct ranges.
#guard
  match (MatrixExpr.matmul (.var_matrix 0 (2, 3))
                           (.var_matrix 1 (3, 4))).materialize with
  | some (_, arity) => arity == 18
  | none => false

/-! Cell selection / out-of-bounds. -/

-- Var matrix cell (r, c) maps to var (base + r*n + c).
#guard
  match (MatrixExpr.var_matrix 0 (2, 3)).lower 1 2 with
  | some (.var i, arity) => i == 5 && arity == 6
  | _ => false

-- Const matrix cell returns the constant at that flat index.
#guard
  match (MatrixExpr.const_matrix (2, 2) [10, 20, 30, 40]).lower 1 0 with
  | some (.const c, _) => c.toNat == 30
  | _ => false

-- Out-of-bounds row.
#guard ((MatrixExpr.var_matrix 0 (2, 3)).lower 2 0).isNone
-- Out-of-bounds col.
#guard ((MatrixExpr.var_matrix 0 (2, 3)).lower 0 3).isNone

/-! Transpose: t(A)[r][c] == A[c][r]. -/

#guard
  match (MatrixExpr.transpose (.var_matrix 0 (2, 3))).lower 2 1 with
  -- t(A) has shape (3, 2); cell (2, 1) is A[1][2] = var (1*3 + 2) = var 5.
  | some (.var i, arity) => i == 5 && arity == 6
  | _ => false

/-! Matmul: cell (0,0) of (1x2)·(2x1) = a[0][0]*b[0][0] + a[0][1]*b[1][0]. -/

-- Evaluate the lowered cell at concrete inputs; check against scalar reference.
-- A = [[3, 5]], B = [[7], [11]]; arity layout: a0=3,a1=5,b0=7,b1=11.
-- Expected: 3*7 + 5*11 = 21 + 55 = 76.
#guard
  match (MatrixExpr.matmul (.var_matrix 0 (1, 2)) (.var_matrix 1 (2, 1))).lower 0 0 with
  | some (e, arity) =>
      arity == 4 && TestEval.eval (envOf [3, 5, 7, 11]) e == 76
  | _ => false

-- 2x2 · 2x2 cell (1, 1) sanity:
-- A = [[1,2],[3,4]], B = [[5,6],[7,8]]; expected (A·B)[1][1] = 3*6 + 4*8 = 50.
#guard
  match (MatrixExpr.matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))).lower 1 1 with
  | some (e, arity) =>
      arity == 8 &&
      TestEval.eval (envOf [1, 2, 3, 4, 5, 6, 7, 8]) e == 50
  | _ => false

-- Transpose interacts: (t(A))·B with A=(2,2)=[[1,2],[3,4]], B=[[5,6],[7,8]]
-- t(A) = [[1,3],[2,4]], so (t(A)·B)[0][1] = 1*6 + 3*8 = 30.
#guard
  match (MatrixExpr.matmul (.transpose (.var_matrix 0 (2, 2)))
                            (.var_matrix 1 (2, 2))).lower 0 1 with
  | some (e, _) => TestEval.eval (envOf [1, 2, 3, 4, 5, 6, 7, 8]) e == 30
  | _ => false

-- Shape-mismatched matmul lowers to none.
#guard ((MatrixExpr.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (4, 5))).lower 0 0).isNone

/-! Hadamard: cell (r, c) = A[r][c] · B[r][c]. -/

-- A = [[1,2],[3,4]], B = [[5,6],[7,8]]; (A ⊙ B)[1][0] = 3*7 = 21.
#guard
  match (MatrixExpr.hadamard (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))).lower 1 0 with
  | some (e, arity) =>
      arity == 8 && TestEval.eval (envOf [1, 2, 3, 4, 5, 6, 7, 8]) e == 21
  | _ => false

-- Shape-mismatched hadamard lowers to none.
#guard ((MatrixExpr.hadamard (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 2))).lower 0 0).isNone

/-! Pointwise scalar: cell (r, c) = A[r][c] · s, constant on the right. -/

-- (3 · A)[0][1] with A = [[1,2],[3,4]] is 2*3 = 6.
#guard
  match (MatrixExpr.pointwise_scalar 3 (.var_matrix 0 (2, 2))).lower 0 1 with
  | some (.mul (.var i) (.const s), arity) =>
      i == 1 && s.toNat == 3 && arity == 4
  | _ => false
