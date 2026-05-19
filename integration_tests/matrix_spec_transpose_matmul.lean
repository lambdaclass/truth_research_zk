-- MatrixExpr spec: (transpose (transpose A)) · B for 2x2 inputs.
-- The matrix-pipeline rule `transpose (transpose x) = x` is expected to
-- collapse the double transpose during saturation; the lowered scalar for
-- output cell (0, 1) then matches the plain (A·B)[0][1].
-- Inputs: A = [x0 x1; x2 x3], B = [x4 x5; x6 x7].
-- Expected: A[0][0]*B[0][1] + A[0][1]*B[1][1] = x0*x5 + x1*x7.
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .matmul (.transpose (.transpose (.var_matrix 0 (2, 2))))
          (.var_matrix 1 (2, 2))

def out : Nat × Nat := (0, 1)
