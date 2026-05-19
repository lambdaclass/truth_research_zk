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

## Further reading

In the optisat repo (https://github.com/lambdaclass/truth_research):

- `ARCHITECTURE.md` — optisat internals
- `LambdaSat/SaturationSpec.lean` — saturation spec
- `LambdaSat/Extraction.lean` — extraction

These also live locally under `.lake/packages/optisat/` after `lake update`.

## Representation-aware rewrites

Montgomery representation is a first-class concept. The mixed rule set
(`RuleSet.babybearMixed`) extends the canonical-only set with:

- **Round-trip elimination** (`to_from_mont`, `from_to_mont`): both
  directions of `to_mont (from_mont _)` and `from_mont (to_mont _)` collapse
  to the inner expression. These are noise-rules whose job is cleanup; they
  fire freely.
- **Cross-repr lowering** (`mul_cross_repr`): a directed rule
  `mul a b → from_mont (mont_mul (to_mont a) (to_mont b))`. Saturation
  introduces the Montgomery realisation on any canonical mul; the round-trip
  rules then collapse the conversions when an inner subexpression is already
  Montgomery (e.g. a chained `mul (mul x y) z` resolves to a chain of
  `mont_mul`s bracketed by one `from_mont` and the leaf `to_mont`s).
- **Trivial constant folds** (`to_mont_zero`, `from_mont_zero`): the
  Montgomery encoding of `0` is `0`, so both conversions collapse on
  literal zero. General `to_mont (.const c) → .const (c · R mod p)` requires
  computed-RHS rule support the engine does not currently provide and is
  deferred to a follow-up.

### Why directed rather than bidirectional

Conversion-elimination is kept as two distinct directed rules
(`to_from_mont` and `from_to_mont`) rather than one bidirectional rule.
Bidirectional cross-repr rules interact pathologically with round-trip
elimination: each firing introduces conversions that the round-trip rules
immediately collapse, growing node count without progress on the e-class
structure. Keeping `mul_cross_repr` single-direction breaks the cycle —
saturation introduces Montgomery realisations on canonical muls, and the
round-trip rules clean up.
