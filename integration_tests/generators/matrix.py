#!/usr/bin/env python3
"""Generate random matrix-spec test vectors over BabyBear.

Each line is `x0 x1 ... xK : y`, where the xs are the row-major flattened
elements of all matrix-variable inputs (in MatrixExpr-declaration order) and
y is the single output cell value mod p. The cell is fixed per op by the
corresponding `matrix_spec_*.lean` file (`def out`).

Unseeded; the checked-in vectors are the frozen artifacts.

    ./matrix.py --op matrix_matmul [-n COUNT]
"""

import argparse
import itertools
import random
import sys

P = 2**31 - 2**27 + 1


def matmul(a, b, m, k, n):
    """Row-major a (m x k) times b (k x n) → m x n list, mod p."""
    out = [0] * (m * n)
    for i in range(m):
        for j in range(n):
            s = 0
            for t in range(k):
                s = (s + a[i * k + t] * b[t * n + j]) % P
            out[i * n + j] = s
    return out


def reference(op: str, xs: list[int]):
    """Return (inputs, outputs) where outputs is the full row-major result."""
    if op == "matrix_matmul":
        assert len(xs) == 8
        return xs, matmul(xs[:4], xs[4:], 2, 2, 2)
    if op == "matrix_matmul_const":
        assert len(xs) == 4
        return xs, matmul(xs, [1, 0, 0, 1], 2, 2, 2)
    if op == "matrix_transpose_matmul":
        # transpose(transpose(A)) · B; rule collapses to plain A · B.
        assert len(xs) == 8
        return xs, matmul(xs[:4], xs[4:], 2, 2, 2)
    raise ValueError(f"unknown op: {op}")


ARITY = {
    "matrix_matmul": 8,
    "matrix_matmul_const": 4,
    "matrix_transpose_matmul": 8,
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--op", required=True, choices=sorted(ARITY))
    parser.add_argument("-n", "--count", type=int, default=None)
    args = parser.parse_args()

    arity = ARITY[args.op]
    it = range(args.count) if args.count is not None else itertools.count()
    try:
        for _ in it:
            xs = [random.randint(0, P - 1) for _ in range(arity)]
            xs_for_bin, ys = reference(args.op, xs)
            rhs = " ".join(str(v) for v in ys)
            print(" ".join(str(v) for v in xs_for_bin) + " : " + rhs, flush=True)
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
