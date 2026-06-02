-- MatrixExpr spec: (2x2) · constant identity matrix, all 4 output cells.
-- Inputs are row-major: A = [x0 x1; x2 x3]; B is the 2x2 identity literal.
-- Expected: A · I = A, so output equals A row-major.
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .matmul (.var_matrix 0 (2, 2)) (.const_matrix (2, 2) [1, 0, 0, 1])
