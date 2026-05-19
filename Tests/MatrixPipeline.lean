import TRZK.MatrixPipeline

open TRZK

-- Identity round-trip with the default rule set, no rule firing.
#guard MatrixPipeline.optimize .default (.var_matrix 0 (2, 3))
    == some (.var_matrix 0 (2, 3))
#guard MatrixPipeline.optimize .default (.const_matrix (2, 2) [0, 1, 2, 3])
    == some (.const_matrix (2, 2) [0, 1, 2, 3])
#guard MatrixPipeline.optimize .default
    (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 4)))
    == some (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 4)))
#guard MatrixPipeline.optimize .default (.transpose (.var_matrix 0 (2, 3)))
    == some (.transpose (.var_matrix 0 (2, 3)))

-- Double-transpose elimination: transpose∘transpose collapses to the inner.
#guard MatrixPipeline.optimize .default
    (.transpose (.transpose (.var_matrix 0 (2, 3))))
    == some (.var_matrix 0 (2, 3))
#guard MatrixPipeline.optimize .default
    (.transpose (.transpose (.transpose (.transpose (.var_matrix 0 (2, 3))))))
    == some (.var_matrix 0 (2, 3))

-- Rule fires under a matmul: t(t(A)) · B = A · B.
#guard MatrixPipeline.optimize .default
    (.matmul (.transpose (.transpose (.var_matrix 0 (2, 3))))
             (.var_matrix 1 (3, 4)))
    == some (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 4)))
