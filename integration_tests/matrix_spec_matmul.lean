-- MatrixExpr spec: (2x2) · (2x2) matmul, output cell (1, 1).
-- Inputs are row-major-flattened: A = [x0 x1; x2 x3], B = [x4 x5; x6 x7].
-- Expected: y = A[1][0]*B[0][1] + A[1][1]*B[1][1] = x2*x5 + x3*x7.
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))

def out : Nat × Nat := (1, 1)
