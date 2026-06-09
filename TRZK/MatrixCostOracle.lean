import TRZK.MatrixOp
import TRZK.MatrixLower
import TRZK.Pipeline

open LambdaSat UnionFind

namespace TRZK

/-! # Matrix cost oracle

    Prices one matrix primitive by what its scalar realisation costs *after*
    field-egraph saturation, instead of the flat per-op-kind table
    (`MatrixOp.localCost`). This is what lets extraction see that constants
    like `1` trivialise downstream muls.

    The oracle is per-primitive: it realises the queried op as a one-level
    `MatrixExpr` over variable/constant children, materialises it to its
    per-cell `ArithExpr`s (`MatrixExpr.materialize`), embeds every cell into
    one field egraph, saturates, and sums the extracted per-cell costs.
    Results are cached in a bounded LRU keyed by
    `(op_kind, child_shapes, sorted_distinct_constants)`. -/

/-- Oracle result type. Matches `localCost : ArithOp → Nat`; sums
    monotonically without overflow. -/
abbrev Cost := Nat

/-- Shapes of the queried node's children, in child order. -/
abbrev ChildShapes := List MatrixShape

/-- Per-child constant payload, in child order: `some entries` when the child
    e-class carries a `const_matrix` (its dense row-major entries), `none`
    for a variable child. -/
abbrev Constants := List (Option (List (BabyBear .canonical)))

/-- Build the single-primitive realisation: the queried op applied to fresh
    leaf children — `const_matrix` where the child class carries constants,
    `var_matrix` otherwise. `none` when the query is malformed (missing child
    shape for an op that needs one). -/
private def realise (op : MatrixOp) (shapes : ChildShapes) (consts : Constants) :
    Option MatrixExpr :=
  let child (i : Nat) : Option MatrixExpr := do
    let s ← shapes[i]?
    match consts[i]? with
    | some (some es) => some (.const_matrix s es)
    | _              => some (.var_matrix i s)
  match op with
  | .const_matrix s es    => some (.const_matrix s es)
  | .var_matrix i s       => some (.var_matrix i s)
  | .matmul _ _           => do some (.matmul (← child 0) (← child 1))
  | .transpose _          => do some (.transpose (← child 0))
  | .ntt n ω _            => do some (.ntt n ω (← child 0))
  | .intt n ω _           => do some (.intt n ω (← child 0))
  | .hadamard _ _         => do some (.hadamard (← child 0) (← child 1))
  | .pointwise_scalar s _ => do some (.pointwise_scalar s (← child 0))

/-- Optimised scalar cost of a materialised grid: embed every cell into one
    field egraph (shared subterms dedup), saturate, and sum the per-cell
    extracted costs. Fuel constants match `Pipeline.optimize`; per-primitive
    fragments are small (design D2). -/
private def gridCost (rules : RuleSet) (grid : MatrixGrid) : Cost :=
  let (roots, g0) :=
    grid.foldl (init := (([] : List EClassId), (.empty : EGraph ArithOp)))
      fun acc row => row.foldl (init := acc) fun (ids, g) cell =>
        let (id, g') := embed g cell
        (id :: ids, g')
  let gSat  := saturateF (fuel := 50) (maxIter := 10) (rebuildFuel := 50) g0 rules
  let gCost := computeCostsF gSat (fun n => NodeOps.localCost n.op) 50
  roots.foldl (init := 0) fun acc id =>
    acc + ((gCost.classes.get? (root gCost.unionFind id)).map (·.bestCost)).getD 0

/-- Price one primitive: realise (D5), materialise, saturate in the field
    egraph, extract. The returned cost is the saturated scalar cost plus the
    output cell count `m·n` — the per-cell writes the loop lowering emits —
    so pure-data ops (`transpose`) price above their collapsed forms instead
    of tying at 0. `var_matrix` prices 0 (inputs are pre-seeded, no writes).
    Malformed queries fall back to the flat `MatrixOp.localCost`.

    The rule set is the canonical-only `RuleSet.babybearNaive`, the same set
    the scalar codegen path saturates with. -/
def oracle (op : MatrixOp) (shapes : ChildShapes) (consts : Constants) : Cost :=
  let priced : Option Cost := do
    let e ← realise op shapes consts
    let (m, n) ← e.shape
    let (grid, _) ← e.materialize
    let writes := match op with
      | .var_matrix _ _ => 0
      | _               => m * n
    pure (gridCost RuleSet.babybearNaive grid + writes)
  priced.getD (MatrixOp.localCost op)

/-! ## Bounded LRU cache -/

/-- Constructor tag for the cache key; the op's cost-relevant payload beyond
    the tag lives in `OracleKey.shapes` (dimensions) and `OracleKey.consts`
    (embedded constants, including NTT twiddles derived from `(n, ω)`). -/
private def kindTag : MatrixOp → Nat
  | .const_matrix _ _     => 0
  | .var_matrix _ _       => 1
  | .matmul _ _           => 2
  | .transpose _          => 3
  | .ntt _ _ _            => 4
  | .intt _ _ _           => 5
  | .hadamard _ _         => 6
  | .pointwise_scalar _ _ => 7

/-- Constants the op itself embeds into its scalar realisation (beyond child
    constants): `const_matrix` entries, the scalar of `pointwise_scalar`, and
    the twiddle sets of `ntt`/`intt` (`{ω^i}` resp. `{n⁻¹·ω⁻ⁱ}` — the values
    the materialised cells bake in, derived from `(n, ω)`). -/
private def opConstants : MatrixOp → List (BabyBear .canonical)
  | .const_matrix _ es    => es
  | .pointwise_scalar c _ => [c]
  | .ntt n ω _            => (List.range n).map fun i => BabyBear.powNat ω i
  | .intt n ω _           =>
      let ωInv : BabyBear .canonical := ⟨ω.val⁻¹⟩
      let nInv : BabyBear .canonical := ⟨(n : ZMod BabyBear.p)⁻¹⟩
      (List.range n).map fun i => nInv * BabyBear.powNat ωInv i
  | _                     => []

/-- Cache key: `(op_kind, child_shapes, sorted_distinct_constants)` (design
    D1). Constants are canonical residues, deduplicated and sorted so
    permutations of the same constant set share an entry; which child carried
    them is deliberately not recorded (design D5). -/
structure OracleKey where
  kind   : Nat
  shapes : List MatrixShape
  consts : List Nat
  deriving Repr, BEq, Hashable

/-- Key of a query: the op's kind tag, the child shapes, and the sorted
    distinct residues of all embedded constants (op-derived ∪ child-carried). -/
def OracleKey.ofQuery (op : MatrixOp) (shapes : ChildShapes)
    (consts : Constants) : OracleKey :=
  let all := opConstants op ++ (consts.filterMap id).flatten
  { kind   := kindTag op
    shapes := shapes
    consts := ((all.map BabyBear.toNat).eraseDups).mergeSort (· ≤ ·) }

/-- Bounded LRU oracle cache. Entries carry a last-use tick; when an insert
    overflows `capacity`, the entry with the smallest tick is evicted (linear
    scan — `capacity` is small). `hits`/`misses` make the hit rate observable. -/
structure OracleCache where
  capacity : Nat := 256
  entries  : Std.HashMap OracleKey (Cost × Nat) := ∅
  tick     : Nat := 0
  hits     : Nat := 0
  misses   : Nat := 0

instance : Inhabited OracleCache := ⟨{}⟩

/-- Evict the least-recently-used entry when over capacity. -/
private def evictLRU (entries : Std.HashMap OracleKey (Cost × Nat))
    (capacity : Nat) : Std.HashMap OracleKey (Cost × Nat) :=
  if entries.size ≤ capacity then entries
  else
    let lru := entries.toList.foldl (init := (none : Option (OracleKey × Nat)))
      fun acc (k, (_, t)) =>
        match acc with
        | none => some (k, t)
        | some (_, tmin) => if t < tmin then some (k, t) else acc
    match lru with
    | some (k, _) => entries.erase k
    | none        => entries

/-- Cached oracle query: on hit, refresh the entry's tick; on miss, run
    `oracle`, insert, and evict the LRU entry if the bound is exceeded. -/
def OracleCache.query (c : OracleCache) (op : MatrixOp) (shapes : ChildShapes)
    (consts : Constants) : Cost × OracleCache :=
  let key := OracleKey.ofQuery op shapes consts
  match c.entries.get? key with
  | some (cost, _) =>
    (cost, { c with entries := c.entries.insert key (cost, c.tick)
                    tick := c.tick + 1, hits := c.hits + 1 })
  | none =>
    let cost := oracle op shapes consts
    let entries := evictLRU (c.entries.insert key (cost, c.tick)) c.capacity
    (cost, { c with entries, tick := c.tick + 1, misses := c.misses + 1 })

/-! ## Per-egraph cost pass

    `MatrixPipeline.optimize` consumes this: resolve each e-class's shape and
    constant payload, then price every node through the cached oracle,
    yielding the cost function `computeCostsF` extracts with. -/

/-- Shape of one node given the child-class shapes resolved so far. -/
private def nodeShape (shapes : Std.HashMap EClassId MatrixShape)
    (uf : UnionFind) : MatrixOp → Option MatrixShape
  | .const_matrix (m, n) es => if es.length = m * n then some (m, n) else none
  | .var_matrix _ s         => some s
  | .matmul l r             => do
      let (m, k1) ← shapes.get? (root uf l)
      let (k2, n) ← shapes.get? (root uf r)
      if k1 = k2 then some (m, n) else none
  | .transpose c            => (shapes.get? (root uf c)).map fun (m, n) => (n, m)
  | .ntt n _ c              => do
      let (rows, cols) ← shapes.get? (root uf c)
      if rows = 1 ∧ cols = n then some (1, n) else none
  | .intt n _ c             => do
      let (rows, cols) ← shapes.get? (root uf c)
      if rows = 1 ∧ cols = n then some (1, n) else none
  | .hadamard l r           => do
      let sa ← shapes.get? (root uf l)
      let sb ← shapes.get? (root uf r)
      if sa = sb then some sa else none
  | .pointwise_scalar _ c   => shapes.get? (root uf c)

private def shapesStep (g : EGraph MatrixOp)
    (shapes : Std.HashMap EClassId MatrixShape) :
    Std.HashMap EClassId MatrixShape × Bool :=
  g.classes.toList.foldl (init := (shapes, false)) fun (acc, changed) (cid, cls) =>
    if acc.contains cid then (acc, changed)
    else
      match cls.nodes.findSome? (fun node => nodeShape acc g.unionFind node.op) with
      | some s => (acc.insert cid s, true)
      | none   => (acc, changed)

private def shapesLoop (g : EGraph MatrixOp) :
    Nat → Std.HashMap EClassId MatrixShape → Std.HashMap EClassId MatrixShape
  | 0, acc => acc
  | fuel + 1, acc =>
    let (acc', changed) := shapesStep g acc
    if changed then shapesLoop g fuel acc' else acc'

/-- Resolve every e-class's matrix shape bottom-up. All nodes of a class
    share one shape (the rewrite rules are shape-preserving), so the first
    resolvable node decides. Classes whose shape cannot be resolved are
    absent from the map and fall back to `MatrixOp.localCost`. -/
def classShapes (g : EGraph MatrixOp) : Std.HashMap EClassId MatrixShape :=
  shapesLoop g (g.classes.size + 1) ∅

/-- Dense entries of every e-class that carries a `const_matrix` node. -/
def classConsts (g : EGraph MatrixOp) :
    Std.HashMap EClassId (List (BabyBear .canonical)) :=
  g.classes.toList.foldl (init := ∅) fun acc (cid, cls) =>
    match cls.nodes.findSome? (fun node =>
        match node.op with
        | .const_matrix _ es => some es
        | _ => none) with
    | some es => acc.insert cid es
    | none    => acc

/-- Price every node in the saturated matrix egraph through the cached
    oracle. Leaves are data, not priced primitives, and bypass the cache:
    `var_matrix` costs 0 (pre-seeded input), `const_matrix` costs its `m·n`
    cell writes — the cache key carries no leaf shape (a leaf has no child
    shapes), so caching them would alias distinct cell counts. Returns the
    per-node cost map (nodes with unresolvable child shapes are absent and
    fall back to `MatrixOp.localCost`) and the cache, whose hit/miss
    counters cover this pass. -/
def oracleNodeCosts (g : EGraph MatrixOp) (cache : OracleCache) :
    Std.HashMap MatrixOp Cost × OracleCache :=
  let shapes := classShapes g
  let consts := classConsts g
  g.classes.toList.foldl (init := ((∅ : Std.HashMap MatrixOp Cost), cache))
    fun acc (_, cls) =>
      cls.nodes.foldl (init := acc) fun (m, c) node =>
        match node.op with
        | .var_matrix _ _          => (m.insert node.op 0, c)
        | .const_matrix (mm, nn) _ => (m.insert node.op (mm * nn), c)
        | _ =>
          let childIds := (NodeOps.children node.op).map (root g.unionFind)
          match childIds.mapM (shapes.get? ·) with
          | none => (m, c)
          | some cshapes =>
            let cconsts := childIds.map (consts.get? ·)
            let (cost, c') := c.query node.op cshapes cconsts
            (m.insert node.op cost, c')

end TRZK
