# TRZK

TRZK compiles Lean specifications of zero-knowledge primitives to optimized
low-level implementations via equality saturation with hardware-aware cost
models.

This cut is a deliberately minimal end-to-end pipeline. Future growth happens
on a working foundation.

## Current abilities

- Expression language: `ArithExpr = Const BabyBear | Var Nat | Add | Sub | Neg | Mul`
- Value type: BabyBear field (`p = 2³¹ − 2²⁷ + 1`) in canonical residue form
- Rewrite rules: `e + 0 → e`, `x + (−x) → 0`, `e * 1 → e`, `e * 0 → 0`,
  `x − x → 0`, `−(−x) → x`
- Rust emitter targeting `u32` BabyBear arithmetic with `u64` intermediates
- CLI `trzk` that turns a `.lean` spec file into a Rust function
- Integration test with crafted and fuzz vectors

## Not yet supported

Multiplicative inverse, multiple representations (Montgomery), multiple fields
(Goldilocks), exponentiation, NTT, ZK primitives. All deferred to future
iterations.

## Dependencies

Saturation is delegated to [optisat / LambdaSat](https://github.com/lambdaclass/truth_research),
a formally verified e-graph + saturation engine. We plug in via typeclass
instances; we do not reimplement the engine.

## Usage

```bash
# Build
lake build

# Compile a spec to Rust
cat > /tmp/spec.lean <<'EOF'
open TRZK (ArithExpr)
def spec : ArithExpr := .add (.var 0) (.const 0)
EOF
./.lake/build/bin/trzk /tmp/spec.lean --output /tmp/out.rs
cat /tmp/out.rs
# → … helper preamble …
#   pub fn arith_spec(x0: u32) -> u32 { x0 }

# Run the integration test
./integration_tests/run.sh --op add0
./integration_tests/run.sh --op add0 --fuzz -n 1000
```

## Pipeline

Four stages, each with one owner:

1. **Parse** — Lean itself. The user writes `def spec : ArithExpr := ...` in a
   `.lean` file; the CLI runs it via `lake env lean --run`.
2. **Saturate** — optisat. Our `ArithOp` type plugs in via `NodeOps` and
   `Extractable` typeclass instances.
3. **Emit** — hand-rolled Rust emitter (`TRZK/Emit.lean`).
4. **Execute** — scripted harness (`integration_tests/`).

See [`docs/pipeline.md`](docs/pipeline.md) for details.

## Layout

| Path | Purpose |
|------|---------|
| `TRZK/ArithExpr.lean` | AST users write specs in |
| `TRZK/ArithOp.lean` | e-graph node + optisat typeclass instances |
| `TRZK/Field/BabyBear.lean` | BabyBear field type, instances, primality |
| `TRZK/Rule.lean` | rewrite rule registry |
| `TRZK/Pipeline.lean` | embed + optimize |
| `TRZK/Emit.lean` | Rust emitter |
| `Compile.lean` | trzk CLI |
| `Tests/*.lean` | `#guard` tests |
| `integration_tests/` | end-to-end harness |
| `docs/` | pipeline, saturation, onboarding, glossary |

## License

See [`LICENSE`](LICENSE).
