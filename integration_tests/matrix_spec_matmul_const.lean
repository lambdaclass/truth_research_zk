-- MatrixExpr spec: (2x2) · constant identity matrix.
-- Inputs are row-major: A = [x0 x1; x2 x3]; B is the 2x2 identity literal.
-- Output cell (0, 1) = A[0][0]*I[0][1] + A[0][1]*I[1][1] = x0*0 + x1*1 = x1.
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .matmul (.var_matrix 0 (2, 2)) (.const_matrix (2, 2) [1, 0, 0, 1])

def out : Nat × Nat := (0, 1)
