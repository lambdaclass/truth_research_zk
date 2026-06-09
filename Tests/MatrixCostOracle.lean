import TRZK.MatrixCostOracle
import TRZK.MatrixPipeline

open TRZK

/-! Tests for the field-egraph cost oracle: pricing, constant-driven
    simplification, extraction wiring, and the bounded LRU cache. -/

/-! ## Leaf and structural-op pricing. -/

-- A bare input prices 0 (pre-seeded, no writes).
#guard oracle (.var_matrix 0 (2, 3)) [] [] == 0

-- A constant prices its cell writes.
#guard oracle (.const_matrix (2, 3) [1, 2, 3, 4, 5, 6]) [] [] == 6

-- Transpose is pure data movement: no scalar cost, only the m·n writes.
#guard oracle (.transpose 0) [(2, 3)] [none] == 6

/-! ## Trivialisable constants lower the price (spec scenario). -/

-- Hadamard with an all-ones operand: every per-cell mul collapses via
-- `mul_one_right`, leaving only the 4 writes.
#guard oracle (.hadamard 0 1) [(2, 2), (2, 2)] [none, some [1, 1, 1, 1]] == 4

-- The same op against a non-trivial constant pays the muls: strictly dearer.
#guard oracle (.hadamard 0 1) [(2, 2), (2, 2)] [none, some [1, 1, 1, 1]]
     < oracle (.hadamard 0 1) [(2, 2), (2, 2)] [none, some [7, 7, 7, 7]]

-- Pointwise scalar 1 vs a non-trivial scalar: same strict ordering.
#guard oracle (.pointwise_scalar 1 0) [(2, 2)] [none]
     < oracle (.pointwise_scalar 3 0) [(2, 2)] [none]

-- Two variable operands pay full price; an all-ones operand undercuts them.
#guard oracle (.hadamard 0 1) [(2, 2), (2, 2)] [none, some [1, 1, 1, 1]]
     < oracle (.hadamard 0 1) [(2, 2), (2, 2)] [none, none]

-- Matmul against the identity simplifies (`mul_zero` + `mul_one` + `add_zero`)
-- below the all-variables matmul of the same shape.
#guard oracle (.matmul 0 1) [(2, 2), (2, 2)] [none, some [1, 0, 0, 1]]
     < oracle (.matmul 0 1) [(2, 2), (2, 2)] [none, none]

/-! ## Extraction correctness on representative shapes: `optimize` (now
    oracle-priced) reconstructs matmuls of various shapes and still collapses
    the rule-driven round trips. -/

#guard MatrixPipeline.optimize .default
    (.matmul (.var_matrix 0 (1, 4)) (.var_matrix 1 (4, 1)))
    == some (.matmul (.var_matrix 0 (1, 4)) (.var_matrix 1 (4, 1)))
#guard MatrixPipeline.optimize .default
    (.matmul (.var_matrix 0 (3, 2)) (.var_matrix 1 (2, 4)))
    == some (.matmul (.var_matrix 0 (3, 2)) (.var_matrix 1 (2, 4)))
#guard MatrixPipeline.optimize .default
    (.matmul (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 2)))
             (.var_matrix 2 (2, 5)))
    == some (.matmul (.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (3, 2)))
                     (.var_matrix 2 (2, 5)))
#guard MatrixPipeline.optimize .default
    (.hadamard (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2)))
    == some (.hadamard (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2)))
#guard MatrixPipeline.optimize .default
    (.pointwise_scalar 3 (.var_matrix 0 (2, 2)))
    == some (.pointwise_scalar 3 (.var_matrix 0 (2, 2)))

-- Double-transpose still collapses: the write term keeps `transpose` priced
-- strictly above its collapsed form, so extraction cannot tie.
#guard MatrixPipeline.optimize .default
    (.transpose (.transpose (.var_matrix 0 (2, 3))))
    == some (.var_matrix 0 (2, 3))

-- iNTT∘NTT round trip collapses under oracle pricing.
#guard MatrixPipeline.optimize (MatrixRuleSet.default.withNttRoundTrip 4 ⟨1⟩)
    (.intt 4 ⟨1⟩ (.ntt 4 ⟨1⟩ (.var_matrix 0 (1, 4))))
    == some (.var_matrix 0 (1, 4))

/-! ## Cache hit-rate observability (spec scenario: repeated queries with the
    same op, shapes, and constant set hit the cache). -/

-- Two same-shaped matmuls share one cache entry: 1 hit, 2 misses (the second
-- matmul hits; the hadamard misses). Leaves bypass the cache.
#guard
  let (_, stats) := MatrixPipeline.optimizeWithStats .default
    (.hadamard (.matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2)))
               (.matmul (.var_matrix 2 (2, 2)) (.var_matrix 3 (2, 2))))
  stats.hits == 1 && stats.misses == 2 && stats.cacheSize == 2

-- Repeated twiddles: two NTTs at the same `(n, ω)` price one saturation.
#guard
  let (_, stats) := MatrixPipeline.optimizeWithStats .default
    (.hadamard (.ntt 4 ⟨1⟩ (.var_matrix 0 (1, 4)))
               (.ntt 4 ⟨1⟩ (.var_matrix 1 (1, 4))))
  stats.hits == 1 && stats.misses == 2

-- Hit rate is observable as an integer percentage.
#guard
  let (_, stats) := MatrixPipeline.optimizeWithStats .default
    (.hadamard (.matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2)))
               (.matmul (.var_matrix 2 (2, 2)) (.var_matrix 3 (2, 2))))
  stats.hitRatePercent == 33

/-! ## Bounded LRU eviction (spec scenario: pathological constant sets cannot
    grow the cache unboundedly). -/

-- Three distinct keys through a capacity-2 cache: size stays at the bound,
-- the evicted key reprices to the same cost on re-query (4 misses, 0 hits).
#guard
  let c0 : OracleCache := { capacity := 2 }
  let (v2, c1)  := c0.query (.pointwise_scalar 2 0) [(2, 2)] [none]
  let (_,  c2)  := c1.query (.pointwise_scalar 3 0) [(2, 2)] [none]
  let (_,  c3)  := c2.query (.pointwise_scalar 4 0) [(2, 2)] [none]
  let (v2', c4) := c3.query (.pointwise_scalar 2 0) [(2, 2)] [none]
  c3.entries.size == 2 && c4.entries.size == 2 &&
    v2 == v2' && c4.misses == 4 && c4.hits == 0

-- LRU order respects recency: hitting an entry refreshes it, so the insert
-- that overflows evicts the *other* (stale) entry.
#guard
  let c0 : OracleCache := { capacity := 2 }
  let (_, c1) := c0.query (.pointwise_scalar 2 0) [(2, 2)] [none]
  let (_, c2) := c1.query (.pointwise_scalar 3 0) [(2, 2)] [none]
  let (_, c3) := c2.query (.pointwise_scalar 2 0) [(2, 2)] [none]  -- hit: refresh
  let (_, c4) := c3.query (.pointwise_scalar 4 0) [(2, 2)] [none]  -- evicts the 3-key
  let (_, c5) := c4.query (.pointwise_scalar 2 0) [(2, 2)] [none]  -- still cached
  c5.hits == 2 && c5.misses == 3
