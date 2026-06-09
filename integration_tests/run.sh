#!/usr/bin/env bash
set -euo pipefail

# Integration test: compile the spec for ${OP} with trzk, link with the Rust
# harness, and verify against reference vectors.
#
# Usage: ./integration_tests/run.sh --op OP [--fuzz] [-n COUNT]
# (run from project root)
#
# Op naming: `<family>_<suffix>`, where <family> ∈ {arith, matrix}.
# Examples: arith_add0, matrix_matmul.
#   <op>'s spec lives at integration_tests/<family>_spec_<suffix>.lean.
#   <op>'s frozen vectors live at integration_tests/test_vectors/<op>/.
#   Matrix ops are compiled with `trzk --matrix`.

OPS=(
    arith_add0 arith_mul arith_mul_chain arith_mul0 arith_sub arith_neg arith_add_neg
    matrix_matmul matrix_matmul_const matrix_transpose_matmul matrix_ntt
    matrix_hadamard matrix_pointwise
)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRZK="$PROJECT_ROOT/.lake/build/bin/trzk"

FUZZ=0
FUZZ_COUNT=""
OP=""
while [ $# -gt 0 ]; do
    case "$1" in
        --fuzz) FUZZ=1; shift ;;
        --op) OP="$2"; shift 2 ;;
        --op=*) OP="${1#--op=}"; shift ;;
        -n) FUZZ_COUNT="$2"; shift 2 ;;
        -n=*) FUZZ_COUNT="${1#-n=}"; shift ;;
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

echo "=== Integration Test: ${OP} via trzk ==="

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
    matrix_hadamard) ARITY=8 ;;
    matrix_pointwise) ARITY=4 ;;
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
if [ "$FUZZ" -eq 1 ]; then
    if [ -n "$FUZZ_COUNT" ]; then
        python3 "$GENERATOR" --op "$OP" -n "$FUZZ_COUNT" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" --fuzz \
            || RESULT=$?
    else
        python3 "$GENERATOR" --op "$OP" \
            | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" --fuzz \
            || RESULT=$?
    fi
else
    cat "$VECTORS_DIR"/*.txt \
        | python3 "$SCRIPT_DIR/verify_arith.py" --binary "$BIN" --arity "$ARITY" \
        || RESULT=$?
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
