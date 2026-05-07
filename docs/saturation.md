# Saturation

TRZK does not implement saturation itself. It delegates to
[optisat / LambdaSat](https://github.com/lambdaclass/truth_research), pinned at
a specific commit in `lakefile.toml`.

## What optisat gives us

- `EGraph Op` — an e-graph parameterized by an `Op` node type (with `children`,
  `mapChildren`, `replaceChildren`, `localCost` provided via the `NodeOps`
  typeclass).
- `RewriteRule Op` — pattern-based rewrite rules. Patterns are `.patVar i` or
  `.node op [children]`.
- `saturateF fuel maxIter rebuildFuel g rules` — fuel-bounded saturation loop.
- `computeCostsF g cost fuel` — cost-model evaluation.
- `extractAuto g root` — lowest-cost extraction from an e-class.

## Brief primer

An **e-graph** is a data structure for storing many equivalent expressions
compactly. Each **e-class** represents an equivalence class of terms; its
**e-nodes** are concrete `Op` instances whose children are e-class ids.

**Saturation** repeatedly applies rewrite rules: every rule match adds new
e-nodes and merges e-classes that become provably equal. When the graph
stabilizes (or fuel runs out), we **extract** the lowest-cost representative
of each class.

## Why a verified backend

Optisat ships proofs that saturation preserves the semantics of the starting
term (modulo a `NodeSemantics` instance). This cut does not yet invoke that
theorem — we use optisat purely for its operational correctness — but the
proof is available for future work.

## Rule audit (BabyBear, naive representation)

Step 1 narrowed the op set to field-relevant ops only and re-audited each
surviving rule for soundness over `ZMod p`:

| Rule              | Status      | Notes                                              |
| ----------------- | ----------- | -------------------------------------------------- |
| `add_zero_right`  | retained    | constant `0` reinterpreted as `(0 : BabyBear)`    |
| `mul_one_right`   | retained    | constant `1` reinterpreted as `(1 : BabyBear)`    |
| `mul_zero_right`  | retained    | constant `0` reinterpreted; arity preserved        |
| `sub_self_zero`   | retained    | sound in any commutative group                     |
| `neg_neg`         | retained    | sound in any group                                 |
| `add_neg_self`    | **new**     | `x + (−x) → 0`; sound in any abelian group        |
| `idiv_one_right`  | dropped     | `idiv` op removed from the field layer             |
| `shl_zero_right`  | dropped     | `shl`/`shr` deferred to step 2 (representation)   |
| `shr_zero_right`  | dropped     | …                                                 |

### Why `mul_inv` and `x · x⁻¹ → 1` are deferred

The rule `x · x⁻¹ → 1` is unsound at `x = 0`: in `ZMod p` the convention is
`(0 : ZMod p)⁻¹ = 0`, so the LHS evaluates to `0` while the RHS is `1`.
Encoding the precondition `x ≠ 0` requires first-class conditional rules
backed by e-class data; that machinery is tracked as items 1 and 2 of
`docs/suggested_features.md` in the upstream optisat repo.

Cost prioritisation against `mul_zero_right` (`0 · x → 0`) does **not** rescue
this: saturation runs both rules to fixpoint regardless of cost. If both fire
on a class containing `0` and the optimizer ever sees `mul_inv 0`, the e-class
for `0` is unioned with the e-class for `1`, breaking soundness. The fix has
to come from the rewrite system (predicate-guarded rules), not from extraction.

Until conditional rules land, `mul_inv` is not exposed as an op at all and no
inverse-related rule ships. This is a pure deferral; the BabyBear pipeline
neither gains nor loses correctness.

## Further reading

In the optisat repo (https://github.com/lambdaclass/truth_research):

- `ARCHITECTURE.md` — optisat internals
- `LambdaSat/SaturationSpec.lean` — saturation spec
- `LambdaSat/Extraction.lean` — extraction

These also live locally under `.lake/packages/optisat/` after `lake update`.
