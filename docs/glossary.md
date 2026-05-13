# Glossary

- **ArithExpr** — TRZK's user-facing AST (`TRZK/ArithExpr.lean`).
  Tree-shaped: `Const (BabyBear .canonical) | Var Nat | Add … | Sub … | Neg … | Mul … | MontMul … | ToMont … | FromMont …`.
- **BabyBear** — finite field of order `p = 2³¹ − 2²⁷ + 1 = 2013265921`,
  defined as `structure BabyBear (r : FieldRepr) where val : ZMod p`
  (`TRZK/Field/BabyBear.lean`).
- **FieldRepr** — the representation tag on a `BabyBear` value:
  `canonical` (residue in `[0, p)`, denotes the field element directly) or
  `montgomery` (the same `ZMod p` value denotes `val · R⁻¹ mod p`).
  Named `FieldRepr` to avoid shadowing Lean's `Repr` typeclass.
- **Montgomery representation** — an alternative encoding of a field element
  `x` as `x · R mod p`, where `R = 2³² mod p`. Addition, subtraction, and
  negation work bit-identically on Montgomery encodings (linear in `x`);
  multiplication requires REDC.
- **R / R²** — the Montgomery radix `R = 2³² mod p` and its square `R² mod p`.
  `R²` is the precomputed constant used by `to_mont` to lift a canonical
  residue to its Montgomery encoding via one REDC.
- **REDC** — Montgomery reduction: given an integer `T < p · R`, returns
  `T · R⁻¹ mod p` in `[0, p)`. Implemented in the generated Rust as
  `bb_redc`.
- **to_mont / from_mont** — explicit e-graph nodes that convert between
  representations. Each carries a nonzero cost so saturation does not insert
  them gratuitously. The round-trip rules `to_mont (from_mont _)` and
  `from_mont (to_mont _)` collapse to the inner expression.
- **mont_mul** — Montgomery-domain multiplication. Distinct e-graph node
  from canonical `mul`, with its own (cheaper) cost. The cross-repr rule
  `mul a b → from_mont (mont_mul (to_mont a) (to_mont b))` introduces it;
  cost-aware extraction selects between canonical and Montgomery realisations
  based on the surrounding expression.
- **ZMod p** — Mathlib's quotient ring `ℤ / pℤ`. A `Field` when `p` is prime.
- **ArithOp** — TRZK's e-graph node type (`TRZK/ArithOp.lean`).
  Flat: children are `EClassId`s, not subtrees. Distinct from `ArithExpr`
  because optisat's engine wants flat nodes; we bridge with `Extractable`.
- **E-graph** — a data structure storing many equivalent expressions
  compactly, as a set of e-classes each containing one or more e-nodes.
- **E-class** — an equivalence class of terms. Identified by an `EClassId`.
- **E-node** — a concrete `Op` instance whose children are e-class ids.
- **Saturation** — repeatedly applying rewrite rules, each match adding new
  e-nodes and merging equivalent e-classes, until the graph stabilizes or
  fuel runs out.
- **Rewrite rule** — a `RewriteRule Op` pairing an `lhs` pattern with an
  `rhs` pattern. Patterns are `.patVar i` (variable placeholder) or
  `.node op [children]`.
- **Extraction** — picking a lowest-cost representative from each e-class,
  yielding a concrete term. We use optisat's `extractAuto`.
- **optisat / LambdaSat** — the upstream verified saturation engine
  (`https://github.com/lambdaclass/truth_research`), pinned via `lakefile.toml`.
