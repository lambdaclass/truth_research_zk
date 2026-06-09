import TRZK.MatrixLower
import TRZK.ArithEval

open TRZK

/-! Tests for the matrix-to-scalar unrolling. -/

/-- Lookup helper for unrolled tests. -/
private def envOf (xs : List Nat) : Nat → BabyBear .canonical
  | i => BabyBear.ofNat (xs.toArray[i]?.getD 0)

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
      arity == 4 &&
      ArithExpr.eval (envOf [3, 5, 7, 11]) e == some (.canon (BabyBear.ofNat 76))
  | _ => false

-- 2x2 · 2x2 cell (1, 1) sanity:
-- A = [[1,2],[3,4]], B = [[5,6],[7,8]]; expected (A·B)[1][1] = 3*6 + 4*8 = 50.
#guard
  match (MatrixExpr.matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))).lower 1 1 with
  | some (e, arity) =>
      arity == 8 &&
      ArithExpr.eval (envOf [1, 2, 3, 4, 5, 6, 7, 8]) e == some (.canon (BabyBear.ofNat 50))
  | _ => false

-- Transpose interacts: (t(A))·B with A=(2,2)=[[1,2],[3,4]], B=[[5,6],[7,8]]
-- t(A) = [[1,3],[2,4]], so (t(A)·B)[0][1] = 1*6 + 3*8 = 30.
#guard
  match (MatrixExpr.matmul (.transpose (.var_matrix 0 (2, 2)))
                            (.var_matrix 1 (2, 2))).lower 0 1 with
  | some (e, _) =>
      ArithExpr.eval (envOf [1, 2, 3, 4, 5, 6, 7, 8]) e == some (.canon (BabyBear.ofNat 30))
  | _ => false

-- Shape-mismatched matmul lowers to none.
#guard ((MatrixExpr.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (4, 5))).lower 0 0).isNone

/-! Montgomery paths: the matrix layer only emits the canonical fragment, so
    exercise `toMont`/`fromMont`/`montMul` at the `ArithExpr` level directly. -/

private def emptyEnv : Nat → BabyBear .canonical := fun _ => 0

-- fromMont ∘ toMont is identity on canonical values.
#guard
  ArithExpr.eval emptyEnv (.fromMont (.toMont (.const (BabyBear.ofNat 12345))))
    == some (.canon (BabyBear.ofNat 12345))

-- toMont ∘ fromMont recovers the same Montgomery value.
#guard
  ArithExpr.eval emptyEnv (.toMont (.fromMont (.toMont (.const (BabyBear.ofNat 12345)))))
    == some (.mont (BabyBear.toMont (BabyBear.ofNat 12345)))

-- montMul on Montgomery operands: (x·R) ⊛ (y·R) = (x·y)·R.
#guard
  ArithExpr.eval emptyEnv
      (.montMul (.toMont (.const (BabyBear.ofNat 3))) (.toMont (.const (BabyBear.ofNat 5))))
    == some (.mont (BabyBear.toMont (BabyBear.ofNat 15)))

-- Domain mismatch: montMul on canonical operands denotes nothing.
#guard
  ArithExpr.eval emptyEnv (.montMul (.const (BabyBear.ofNat 3)) (.const (BabyBear.ofNat 5)))
    == none

-- Domain mismatch: linear op across representations denotes nothing.
#guard
  ArithExpr.eval emptyEnv (.add (.const (BabyBear.ofNat 3)) (.toMont (.const (BabyBear.ofNat 5))))
    == none
