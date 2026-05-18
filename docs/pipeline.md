# Pipeline

Four stages, each independently replaceable.

## 1. Parse — Lean

The user writes a spec file such as `integration_tests/arith_spec_add0.lean`:

```lean
open TRZK (ArithExpr)
def spec : ArithExpr := .add (.var 0) (.const 0)
```

The CLI (`Compile.lean:main`) reads this file, strips its `import` lines, and
wraps it in a runner script that imports `TRZK` and adds a `main`. Lean's
elaborator performs the actual parse via `lake env lean --run`.

**Input**: `.lean` source with `def spec : ArithExpr := ...`.
**Output**: an in-memory `ArithExpr` value.

## 2. Saturate — optisat

The runner calls `TRZK.optimize` (`TRZK/Pipeline.lean`), which:

1. Embeds the `ArithExpr` into an empty `EGraph ArithOp` (`embed`).
2. Runs `LambdaSat.saturateF` with the rules in `TRZK.allRules`.
3. Computes costs via `computeCostsF`.
4. Extracts the lowest-cost form via `extractAuto`.

The bridge between our world and optisat's lives entirely in
`TRZK/ArithOp.lean`:

- `ArithOp` — e-graph node type (children are `EClassId`s)
- `NodeOps ArithOp` — the four structural obligations, all discharged by
  `cases op <;> simp`-style one-liners
- `Extractable ArithOp ArithExpr` — reconstructs an `ArithExpr` from a
  saturated e-class

**Input**: `ArithExpr`.
**Output**: `Option ArithExpr` (the lowest-cost equivalent form).

## 3. Emit — hand-rolled

`TRZK/Emit.lean` turns an `ArithExpr` into a Rust string:

- `usedVarsAux` — boolean array of length `arity` marking referenced vars
- `emitHelpers` — preamble defining `const P`, the Montgomery constants
  (`R`, `R_SQUARED`, `P_INV_NEG`), and the helpers `bb_add`, `bb_sub`,
  `bb_neg`, `bb_mul`, `bb_redc`, `bb_to_mont`, `bb_from_mont`,
  `bb_mont_mul`, and Montgomery aliases `bb_mont_add` / `bb_mont_sub` /
  `bb_mont_neg` (which alias the canonical add/sub/neg because Montgomery
  encoding is linear in `x`). All naive: `u32` params, `u64` intermediates,
  explicit reductions back into `[0, p)`. Performance tuning is a separate
  workstream.
- `emitExpr` — `u32` BabyBear expression; constants are canonical residues,
  ops delegate to the helpers (canonical ops to `bb_*`, Montgomery ops to
  `bb_mont_mul` / `bb_to_mont` / `bb_from_mont`)
- `emitFunction name arity e` — full `pub fn <name>(...) -> u32 { ... }` with
  the helper preamble prepended

**Input**: `ArithExpr`.
**Output**: a `String` of Rust source.

Values flow as canonical residues in `[0, p)` at the function boundary:
the caller passes canonical `u32`s in and gets a canonical `u32` out.
Inside the function body, the optimizer may have selected the Montgomery
realisation for some subexpressions; the `to_mont` / `from_mont` ops wrap
those subexpressions so the boundary contract is preserved. Per-parameter
Montgomery contracts (so a hot-path kernel can accept already-Montgomery
inputs) are planned.

## Representation as a first-class concept

The BabyBear value type carries a `FieldRepr` tag — `BabyBear .canonical` or
`BabyBear .montgomery` — and the AST distinguishes canonical and Montgomery
realisations of the same field element via:

- `to_mont` / `from_mont`: explicit conversion ops with nonzero cost
- `mont_mul`: Montgomery-domain multiplication, distinct from canonical `mul`

The egraph holds both realisations of a value in the same e-class, and
cost-aware extraction picks one per subterm. Operations that are linear in
the underlying value (`add`, `sub`, `neg`) work bit-identically on either
representation and have a single AST node each; only `mul` needs a
representation-specific variant because canonical mul plus modular
reduction differs from a Montgomery REDC step.

For details on the rules that drive cross-representation rewrites and the
cost-model behaviour that makes Montgomery competitive for chained
multiplications, see `docs/saturation.md`.

## 4. Execute — scripts

`integration_tests/run.sh` orchestrates:

1. `lake build trzk`
2. `trzk <spec> --output <scriptdir>/generated.rs`
3. `rustc -O --edition 2024 harness.rs -o <bin>` with `--cfg arity="N"` and
   `--cfg field="babybear"` to select the matching call signature.
4. Pipe crafted vectors (or a generator for `--fuzz`) into
   `verify_arith.py --binary ... --arity N`.

**Input**: a `.lean` spec.
**Output**: pass/fail exit code.
