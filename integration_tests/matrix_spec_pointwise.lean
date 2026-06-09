-- MatrixExpr spec: pointwise scalar multiplication 3 · A of a (2x2) matrix,
-- all 4 output cells. Input is row-major-flattened: A = [x0 x1; x2 x3].
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .pointwise_scalar 3 (.var_matrix 0 (2, 2))
