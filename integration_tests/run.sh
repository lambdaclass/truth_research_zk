#!/usr/bin/env bash
set -euo pipefail

# Integration test: compile the spec for ${OP} with trzk, link with the Rust
# harness, and verify against reference vectors.
#
# Usage: ./integration_tests/run.sh --op OP [--fuzz] [-n COUNT] [--mutate]
# (run from project root)
#
# Op naming: `<family>_<suffix>`, where <family> ∈ {arith, matrix}.
# Examples: arith_add0, matrix_matmul.
#   <op>'s spec lives at integration_tests/<family>_spec_<suffix>.lean.
#   <op>'s frozen vectors live at integration_tests/test_vectors/<op>/.
#   Matrix ops are compiled with `trzk --matrix`.
#
# NTT-family ops are additionally verified against the Plonky3-backed
# p3_oracle (built via cargo, pinned deps): in frozen mode the kernel is
# checked against both the frozen Python-generated vectors and the oracle's
# recomputed outputs; in fuzz mode the generator stream is piped through
# `p3_oracle --check`, which cross-checks the Python reference against
# Plonky3 on every vector before the kernel comparison.
#
# --mutate (NTT-family only): corrupt the generated kernel with an
# output-index swap and assert that BOTH verification legs fail. A
# differential check that cannot be shown to fail is not evidence.

OPS=(
    arith_add0 arith_mul arith_mul_chain arith_mul0 arith_sub arith_neg arith_add_neg
    matrix_matmul matrix_matmul_const matrix_transpose_matmul matrix_ntt
)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"

FUZZ=0
FUZZ_COUNT=""
OP=""
MUTATE=0
while [ $# -gt 0 ]; do
    case "$1" in
        --fuzz) FUZZ=1; shift ;;
        --op) OP="$2"; shift 2 ;;
        --op=*) OP="${1#--op=}"; shift ;;
        -n) FUZZ_COUNT="$2"; shift 2 ;;
        -n=*) FUZZ_COUNT="${1#-n=}"; shift ;;
        --mutate) MUTATE=1; shift ;;
        *) echo "Unknown arg: $1" >&2; exit 2 ;;
    esac
done

if [ -z "$OP" ]; then
    echo "--op is required. Registered ops: ${OPS[*]}" >&2
    exit 2
fi

found=0
for o in "${OPS[@]}"; do
    if [ "$o" = "$OP" ]; then found=1; fi
done
if [ "$found" -eq 0 ]; then
    echo "Unknown --op $OP. Registered ops: ${OPS[*]}" >&2
    exit 2
fi

# Family dispatch: matrix ops pass `--matrix` to trzk and use generators/matrix.py.
case "$OP" in
    matrix_*)
        IS_MATRIX=1
        SUFFIX="${OP#matrix_}"
        SPEC="$SCRIPT_DIR/matrix_spec_${SUFFIX}.lean"
        GENERATOR="$SCRIPT_DIR/generators/matrix.py"
        ;;
    arith_*)
        IS_MATRIX=0
        SUFFIX="${OP#arith_}"
        SPEC="$SCRIPT_DIR/arith_spec_${SUFFIX}.lean"
        GENERATOR="$SCRIPT_DIR/generators/arith.py"
        ;;
    *)
        echo "Internal error: op '$OP' has no family prefix" >&2; exit 2 ;;
esac

GEN_RS="$SCRIPT_DIR/generated.rs"
BIN="/tmp/trzk_${OP}"
VECTORS_DIR="$SCRIPT_DIR/test_vectors/${OP}"

# NTT-family registry: ops verified against the Plonky3 oracle in addition
# to the Python reference. P3_OP/P3_N map the harness op onto the oracle's
# transform and size.
case "$OP" in
    matrix_ntt) P3_OP="ntt"; P3_N=8 ;;
    *) P3_OP="" ;;
esac

if [ "$MUTATE" -eq 1 ] && [ -z "$P3_OP" ]; then
    echo "--mutate is only supported for NTT-family ops (got $OP)" >&2
    exit 2
fi
if [ "$MUTATE" -eq 1 ] && [ "$FUZZ" -eq 1 ]; then
    echo "--mutate uses frozen vectors; drop --fuzz" >&2
    exit 2
fi

echo "=== Integration Test: ${OP} via trzk ==="

# Build the Plonky3 oracle for NTT-family ops. --target-dir keeps the binary
# at a deterministic path regardless of any global cargo build-cache config.
ORACLE_BIN=""
if [ -n "$P3_OP" ]; then
    echo "Building p3_oracle..."
    cargo build --release --locked --quiet \
        --manifest-path "$SCRIPT_DIR/p3_oracle/Cargo.toml" \
        --target-dir "$SCRIPT_DIR/p3_oracle/target"
    ORACLE_BIN="$SCRIPT_DIR/p3_oracle/target/release/p3_oracle"
fi

# 1. Build unconditionally (cheap when up-to-date). `lake build` resolves to
# defaultTargets (TRZK, Tests, trzk); the trzk runner re-elaborates a temp
# file via `lake env lean --run`, so the TRZK lib oleans must be on disk.
(cd "$PROJECT_ROOT" && lake build)

# 2. Generate Rust from spec.
echo "Generating Rust from ${SPEC##*/}..."
if [ "$IS_MATRIX" -eq 1 ]; then
    "$TRZK" "$SPEC" --matrix --name "arith_spec" --output "$GEN_RS"
else
    "$TRZK" "$SPEC" --name "arith_spec" --output "$GEN_RS"
fi

# Corrupt the kernel: swap two output indices just before the return. The
# pattern is anchored to the emitter's final `out` return; if the emitter
# shape changes, the assert fails loudly instead of silently not corrupting
# (which would flip the mutation check's meaning).
if [ "$MUTATE" -eq 1 ]; then
    echo "Injecting output-index swap into ${GEN_RS##*/}..."
    python3 - "$GEN_RS" <<'EOF'
import re, sys

path = sys.argv[1]
with open(path) as f:
    src = f.read()
new, count = re.subn(r"\n    out\n\}\s*$", "\n    out.swap(0, 1);\n    out\n}\n", src)
assert count == 1, "kernel return shape not found; cannot inject corruption"
with open(path, "w") as f:
    f.write(new)
EOF
fi

# Arity per op. The harness picks an arity-specific arm via `--cfg arity="N"`;
# `--cfg field="..."` selects the field. Matrix-op arity is the flat input
# count across all matrix variables in row-major declaration order.
case "$OP" in
    arith_add0) ARITY=1 ;;
    arith_mul) ARITY=2 ;;
    arith_mul_chain) ARITY=4 ;;
    arith_mul0) ARITY=1 ;;
    arith_sub) ARITY=2 ;;
    arith_neg) ARITY=1 ;;
    arith_add_neg) ARITY=1 ;;
    matrix_matmul) ARITY=8 ;;
    matrix_matmul_const) ARITY=4 ;;
    matrix_transpose_matmul) ARITY=8 ;;
    matrix_ntt) ARITY=8 ;;
    *) echo "Internal error: no arity registered for op '$OP'" >&2; exit 2 ;;
esac

FIELD="babybear"

# 3. Compile harness (which #[path]s the generated file).
echo "Compiling..."
MATRIX_CFG=()
if [ "$IS_MATRIX" -eq 1 ]; then
    MATRIX_CFG=(--cfg "matrix")
fi
rustc -O --edition 2024 \
    --check-cfg 'cfg(arity, values("1", "2", "4", "8"))' \
    --check-cfg 'cfg(field, values("babybear"))' \
    --check-cfg 'cfg(matrix)' \
    --cfg "arity=\"${ARITY}\"" \
    --cfg "field=\"${FIELD}\"" \
    "${MATRIX_CFG[@]}" \
    "$SCRIPT_DIR/harness.rs" -o "$BIN"

# 4. Verify.
RESULT=0
if [ "$MUTATE" -eq 1 ]; then
    # Both legs must catch the corrupted kernel; the verifier exiting zero on
    # either leg means the differential check cannot fail and is not evidence.
    PY_RESULT=0
    cat "$VECTORS_DIR"/*.txt \
        | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" \
        || PY_RESULT=$?
    P3_RESULT=0
    cat "$VECTORS_DIR"/*.txt \
        | "$ORACLE_BIN" --op "$P3_OP" --n "$P3_N" --check \
        | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" \
        || P3_RESULT=$?
    if [ "$PY_RESULT" -ne 0 ] && [ "$P3_RESULT" -ne 0 ]; then
        echo "Mutation check: corrupted kernel caught by both references."
    else
        echo "Mutation check FAILED: corrupted kernel passed verification" \
            "(python exit $PY_RESULT, plonky3 exit $P3_RESULT)" >&2
        RESULT=1
    fi
elif [ "$FUZZ" -eq 1 ]; then
    # For NTT-family ops the generator stream passes through the oracle:
    # `--check` fails on any Python-vs-Plonky3 disagreement, then the kernel
    # is verified against the (agreed) expected outputs.
    P3_PIPE=(cat)
    if [ -n "$P3_OP" ]; then
        P3_PIPE=("$ORACLE_BIN" --op "$P3_OP" --n "$P3_N" --check)
    fi
    if [ -n "$FUZZ_COUNT" ]; then
        python3 "$GENERATOR" --op "$OP" -n "$FUZZ_COUNT" \
            | "${P3_PIPE[@]}" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" --fuzz \
            || RESULT=$?
    else
        python3 "$GENERATOR" --op "$OP" \
            | "${P3_PIPE[@]}" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" --fuzz \
            || RESULT=$?
    fi
else
    cat "$VECTORS_DIR"/*.txt \
        | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" \
        || RESULT=$?
    if [ -n "$P3_OP" ] && [ "$RESULT" -eq 0 ]; then
        # Plonky3 leg: recompute the frozen vectors' expected outputs with the
        # oracle (--check also re-certifies python==plonky3 on the frozen set)
        # and verify the kernel against them.
        cat "$VECTORS_DIR"/*.txt \
            | "$ORACLE_BIN" --op "$P3_OP" --n "$P3_N" --check \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" \
            || RESULT=$?
    fi
fi

# 5. Cleanup.
rm -f "$GEN_RS" "$BIN"
rm -rf "$SCRIPT_DIR/artifacts"

if [ $RESULT -eq 0 ]; then
    echo "=== Integration test PASSED (op ${OP}) ==="
else
    echo "=== Integration test FAILED (op ${OP}) ==="
fi
exit $RESULT
