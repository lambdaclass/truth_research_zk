#!/usr/bin/env python3
"""Generate random ArithExpr test vectors over BabyBear.

Emits `x0 [x1 ...] : y` per line, where every value is a canonical residue in
`[0, p)` and the reference output `y` is computed mod p in Python to match the
spec being exercised. Unseeded by default (the checked-in vectors are frozen
artifacts).

    ./arith.py --op arith_add0 [-n COUNT]
"""

import argparse
import itertools
import random
import sys

# BabyBear prime p = 2^31 - 2^27 + 1.
P = 2**31 - 2**27 + 1

# Arity per op. Keys are the full op identifiers as accepted by run.sh.
ARITY = {
    "arith_add0": 1,
    "arith_mul": 2,
    "arith_mul_chain": 4,
    "arith_mul0": 1,
    "arith_sub": 2,
    "arith_neg": 1,
    "arith_add_neg": 1,
}


def reference(op: str, xs: list[int]) -> int:
    if op == "arith_add0":
        # arith_spec_add0: y = x0 + 0 = x0 (mod p).
        return xs[0] % P
    if op == "arith_mul":
        # arith_spec_mul: y = (x0 * 1) * x1 → x0 * x1 (mod p).
        return (xs[0] * xs[1]) % P
    if op == "arith_mul_chain":
        # arith_spec_mul_chain: y = x0 * x1 * x2 * x3 (mod p). The optimizer
        # selects the Montgomery realisation internally; the function-boundary
        # contract is still canonical residues in / canonical residue out.
        return (xs[0] * xs[1] * xs[2] * xs[3]) % P
    if op == "arith_mul0":
        # arith_spec_mul0: y = x0 * 0 = 0. Optimizer eliminates x0; arity 1
        # preserved.
        return 0
    if op == "arith_sub":
        # arith_spec_sub: y = x0 - x1 (mod p).
        return (xs[0] - xs[1]) % P
    if op == "arith_neg":
        # arith_spec_neg: y = -x0 (mod p).
        return (-xs[0]) % P
    if op == "arith_add_neg":
        # arith_spec_add_neg: y = x0 + (-x0) = 0.
        return 0
    raise ValueError(f"unknown op: {op}")


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
            y = reference(args.op, xs)
            print(" ".join(str(v) for v in xs) + " : " + str(y), flush=True)
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
