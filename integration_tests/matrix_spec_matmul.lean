-- MatrixExpr spec: (2x2) · (2x2) matmul, all 4 output cells.
-- Inputs are row-major-flattened: A = [x0 x1; x2 x3], B = [x4 x5; x6 x7].
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))
