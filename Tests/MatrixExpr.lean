import TRZK.MatrixExpr

open TRZK

-- Size counts AST nodes.
#guard MatrixExpr.size (.var_matrix 0 (2, 3)) == 1
#guard MatrixExpr.size (.const_matrix (2, 2) [0, 1, 2, 3]) == 1
#guard MatrixExpr.size
    (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 4))) == 3
#guard MatrixExpr.size (.transpose (.var_matrix 0 (2, 3))) == 2

-- Structural inequality.
#guard (MatrixExpr.var_matrix 0 (2, 3)) != .var_matrix 0 (3, 2)
#guard (MatrixExpr.var_matrix 0 (2, 3)) != .var_matrix 1 (2, 3)
#guard (MatrixExpr.transpose (.var_matrix 0 (2, 3)))
    != .var_matrix 0 (2, 3)

-- Shape derivation: leaves.
#guard MatrixExpr.shape (.var_matrix 0 (2, 3)) == some (2, 3)
#guard MatrixExpr.shape (.const_matrix (2, 2) [0, 1, 2, 3]) == some (2, 2)
#guard MatrixExpr.shape (.const_matrix (2, 3) [0, 1, 2]) == none

-- Shape derivation: matmul agrees on inner dim.
#guard MatrixExpr.shape
    (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 4))) == some (2, 4)
#guard MatrixExpr.shape
    (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (4, 5))) == none

-- Shape derivation: transpose swaps axes.
#guard MatrixExpr.shape (.transpose (.var_matrix 0 (2, 3))) == some (3, 2)
#guard MatrixExpr.shape (.transpose (.transpose (.var_matrix 0 (2, 3))))
    == some (2, 3)

-- Shape derivation propagates `none` through subexpressions.
#guard MatrixExpr.shape
    (.matmul (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (4, 5)))
             (.var_matrix 2 (5, 6))) == none

-- Shape derivation: hadamard requires equal shapes; pointwise passes through.
#guard MatrixExpr.shape
    (.hadamard (.var_matrix 0 (2, 3)) (.var_matrix 1 (2, 3))) == some (2, 3)
#guard MatrixExpr.shape
    (.hadamard (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 2))) == none
#guard MatrixExpr.shape
    (.pointwise_scalar 3 (.var_matrix 0 (2, 3))) == some (2, 3)

-- Size counts the new constructors' nodes.
#guard MatrixExpr.size
    (.hadamard (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))) == 3
#guard MatrixExpr.size (.pointwise_scalar 3 (.var_matrix 0 (2, 2))) == 2
