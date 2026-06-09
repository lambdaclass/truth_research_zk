import TRZK.MatrixOp
import TRZK.MatrixCostOracle

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

/-- iNTT-NTT round-trip at fixed `(n, ω)`: `intt n ω (ntt n ω x) → x`. The
    pattern matches by op-equality, so distinct `(n, ω)` parameters
    produce distinct nodes and the rule only fires on a matching pair. -/
def inttNttRoundTrip (n : Nat) (ω : BabyBear .canonical) : RewriteRule MatrixOp where
  name := s!"intt_ntt_round_trip_{n}"
  lhs := .node (.intt n ω 0) [.node (.ntt n ω 0) [.patVar 0]]
  rhs := .patVar 0

/-- NTT-iNTT round-trip at fixed `(n, ω)`: `ntt n ω (intt n ω x) → x`. -/
def nttInttRoundTrip (n : Nat) (ω : BabyBear .canonical) : RewriteRule MatrixOp where
  name := s!"ntt_intt_round_trip_{n}"
  lhs := .node (.ntt n ω 0) [.node (.intt n ω 0) [.patVar 0]]
  rhs := .patVar 0

/-- Default matrix rule set: structural rules that are always-on regardless
    of NTT parameters. NTT round-trip rules are size-and-root specific and
    callers add them via `MatrixRuleSet.withNttRoundTrip`. -/
def MatrixRuleSet.default : MatrixRuleSet := [transposeTranspose]

/-- Extend a rule set with NTT round-trip rules for a specific `(n, ω)`. -/
def MatrixRuleSet.withNttRoundTrip (rules : MatrixRuleSet)
    (n : Nat) (ω : BabyBear .canonical) : MatrixRuleSet :=
  rules ++ [inttNttRoundTrip n ω, nttInttRoundTrip n ω]

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
  | .ntt n ω a         =>
    let (ia, g1) := embedMatrix g a
    g1.add ⟨.ntt n ω ia⟩
  | .intt n ω a        =>
    let (ia, g1) := embedMatrix g a
    g1.add ⟨.intt n ω ia⟩
  | .hadamard a b      =>
    let (ia, g1) := embedMatrix g a
    let (ib, g2) := embedMatrix g1 b
    g2.add ⟨.hadamard ia ib⟩
  | .pointwise_scalar s a =>
    let (ia, g1) := embedMatrix g a
    g1.add ⟨.pointwise_scalar s ia⟩

namespace MatrixPipeline

/-- Oracle-cache observability for one `optimize` run: hit/miss counters and
    the cache's end-of-run entry count. `hitRatePercent` is the integer
    percentage CI asserts on. -/
structure OracleStats where
  hits      : Nat
  misses    : Nat
  cacheSize : Nat
  deriving Repr, BEq, Inhabited

/-- Integer cache hit rate in percent (0 when no queries ran). -/
def OracleStats.hitRatePercent (s : OracleStats) : Nat :=
  if s.hits + s.misses = 0 then 0 else s.hits * 100 / (s.hits + s.misses)

/-- End-to-end matrix optimization: embed → saturate → price every node
    through the cached field-egraph cost oracle → extract. Nodes the oracle
    cannot price (unresolvable child shapes) fall back to the flat
    `MatrixOp.localCost`. Also returns the oracle's cache statistics. -/
def optimizeWithStats (rules : MatrixRuleSet) (expr : MatrixExpr)
    (cache : OracleCache := {}) : Option MatrixExpr × OracleStats :=
  let (rootId, g0) := embedMatrix .empty expr
  let g_sat  := saturateF (fuel := 50) (maxIter := 10) (rebuildFuel := 50) g0 rules
  let (costs, cache') := oracleNodeCosts g_sat cache
  let g_cost := computeCostsF g_sat
    (fun n => costs.getD n.op (NodeOps.localCost n.op)) 50
  (extractAuto g_cost rootId,
   { hits := cache'.hits, misses := cache'.misses,
     cacheSize := cache'.entries.size })

/-- `optimizeWithStats` without the cache statistics. -/
def optimize (rules : MatrixRuleSet) (expr : MatrixExpr) : Option MatrixExpr :=
  (optimizeWithStats rules expr).1

end MatrixPipeline

end TRZK
