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
- `emitHelpers` — preamble defining `const P` and helpers `bb_add`, `bb_sub`,
  `bb_neg`, `bb_mul`. Naive canonical reduction: `u32` params, `u64`
  intermediates, explicit reduction back into `[0, p)`.
- `emitExpr` — `u32` BabyBear expression; constants are canonical residues,
  ops delegate to the helpers
- `emitFunction name arity e` — full `pub fn <name>(...) -> u32 { ... }` with
  the helper preamble prepended

**Input**: `ArithExpr`.
**Output**: a `String` of Rust source.

Values flow as canonical residues in `[0, p)` end-to-end: BabyBear constants
on the Lean side, decimal `u32` strings at the harness boundary, `u32`
arguments and return value in the generated kernel.

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
