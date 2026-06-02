-- MatrixExpr spec: (transpose (transpose A)) · B for 2x2 inputs, all 4 output cells.
-- The matrix-pipeline rule `transpose (transpose x) = x` is expected to
-- collapse the double transpose during saturation; all cells then match plain A·B.
-- Inputs: A = [x0 x1; x2 x3], B = [x4 x5; x6 x7].
open TRZK (MatrixExpr)

def spec : MatrixExpr :=
  .matmul (.transpose (.transpose (.var_matrix 0 (2, 2))))
          (.var_matrix 1 (2, 2))
