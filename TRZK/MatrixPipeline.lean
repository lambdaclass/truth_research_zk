import TRZK.MatrixOp

open LambdaSat

namespace TRZK

/-- Rule set consumed by `MatrixPipeline.optimize`. -/
abbrev MatrixRuleSet := List (RewriteRule MatrixOp)

/-- Double-transpose elimination: `transpose (transpose x) → x`. Cheap and
    always sound; the first rewrite rule wired into the matrix pipeline. -/
def transposeTranspose : RewriteRule MatrixOp where
  name := "transpose_transpose"
  lhs := .node (.transpose 0) [.node (.transpose 0) [.patVar 0]]
  rhs := .patVar 0

/-- Default matrix rule set: double-transpose elimination only. -/
def MatrixRuleSet.default : MatrixRuleSet := [transposeTranspose]

/-- Recursively embed a `MatrixExpr` into an `EGraph<MatrixOp>`.
    Returns the root e-class id and the updated graph. -/
partial def embedMatrix (g : EGraph MatrixOp) :
    MatrixExpr → (EClassId × EGraph MatrixOp)
  | .const_matrix s es => g.add ⟨.const_matrix s es⟩
  | .var_matrix i s    => g.add ⟨.var_matrix i s⟩
  | .matmul a b        =>
    let (ia, g1) := embedMatrix g a
    let (ib, g2) := embedMatrix g1 b
    g2.add ⟨.matmul ia ib⟩
  | .transpose a       =>
    let (ia, g1) := embedMatrix g a
    g1.add ⟨.transpose ia⟩

namespace MatrixPipeline

/-- End-to-end matrix optimization: embed → saturate → extract.

    Flat per-op cost from `NodeOps.localCost` is a placeholder; the
    field-egraph cost oracle replaces it in a later sub-change. -/
def optimize (rules : MatrixRuleSet) (expr : MatrixExpr) : Option MatrixExpr :=
  let (rootId, g0) := embedMatrix .empty expr
  let g_sat  := saturateF (fuel := 50) (maxIter := 10) (rebuildFuel := 50) g0 rules
  let g_cost := computeCostsF g_sat (fun n => NodeOps.localCost n.op) 50
  extractAuto g_cost rootId

end MatrixPipeline

end TRZK
