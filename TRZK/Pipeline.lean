import TRZK.ArithOp
import TRZK.Rule

open LambdaSat

namespace TRZK

/-- Recursively embed an `ArithExpr` into an `EGraph`.
    Returns the root e-class id and the updated graph. -/
partial def embed (g : EGraph ArithOp) : ArithExpr → (EClassId × EGraph ArithOp)
  | .const n     => g.add ⟨.const n⟩
  | .var i       => g.add ⟨.var i⟩
  | .add a b     =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.add ia ib⟩
  | .sub a b     =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.sub ia ib⟩
  | .neg a       =>
    let (ia, g1) := embed g a
    g1.add ⟨.neg ia⟩
  | .mul a b     =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.mul ia ib⟩
  | .montMul a b =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.montMul ia ib⟩
  | .toMont a    =>
    let (ia, g1) := embed g a
    g1.add ⟨.toMont ia⟩
  | .fromMont a  =>
    let (ia, g1) := embed g a
    g1.add ⟨.fromMont ia⟩

/-- End-to-end optimization: embed → saturate → extract lowest-cost form.
    Fuel constants (50, 10, 50) are sized for v0 with a single rule; revisit
    when rules can explode the graph.

    Cost is `NodeOps.localCost` (per-op, not children-aware). Calibration is
    deferred (design D5 / R4): the relative weights ensure Montgomery mul is
    preferred over canonical mul, but absolute numbers are guesses. -/
def optimize (rules : RuleSet) (expr : ArithExpr) : Option ArithExpr :=
  let (rootId, g0) := embed .empty expr
  let g_sat  := saturateF (fuel := 50) (maxIter := 10) (rebuildFuel := 50) g0 rules
  let g_cost := computeCostsF g_sat (fun n => NodeOps.localCost n.op) 50
  extractAuto g_cost rootId

end TRZK
