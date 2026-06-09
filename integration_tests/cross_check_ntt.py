#!/usr/bin/env python3
"""Cross-check the Python NTT reference against the Plonky3 oracle.

Two independent references back the NTT-family ops: the naive Python NTT in
`generators/matrix.py` (which freezes vectors) and the Plonky3-backed
`p3_oracle` binary. This script proves they are the *same transform* — same
root, same output order, same `intt` normalization — on crafted vectors at
every supported size, before any frozen vector is trusted. A convention
mismatch between references is a different transform that can still agree on
degenerate inputs, so the crafted set includes basis vectors (which expose the
full twiddle row and any output permutation), constants, ramps, and
worst-case residues.

Checks per size, for both `ntt` and `intt`:
  1. `p3_oracle --check` accepts `inputs : python_outputs` lines (the oracle's
     own comparison fails the run on any disagreement).
  2. The oracle's stdout outputs equal the Python outputs (direct comparison,
     independent of the oracle's exit code).
  3. Round-trip: oracle `intt` of the Python `ntt` outputs returns the inputs.

Usage:
    ./cross_check_ntt.py --oracle p3_oracle/target/release/p3_oracle
"""

import argparse
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "generators"))
from matrix import P, ntt, ntt_omega  # noqa: E402

SIZES = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]


def intt(xs: list[int], n: int) -> list[int]:
    """Inverse of `matrix.ntt` per the TRZK convention (`inttCell` in
    `TRZK/MatrixLower.lean`): y[k] = n⁻¹·Σⱼ x[j]·ω^(-j·k) mod p."""
    omega_inv = pow(ntt_omega(n), P - 2, P)
    n_inv = pow(n, P - 2, P)
    return [
        n_inv * sum(xs[j] * pow(omega_inv, j * k, P) for j in range(n)) % P
        for k in range(n)
    ]


def crafted(n: int) -> list[list[int]]:
    """Deterministic vectors chosen to expose convention mismatches."""
    basis = [[1 if j == i else 0 for j in range(n)] for i in (0, 1, n - 1)]
    return basis + [
        [0] * n,
        [1] * n,
        [P - 1] * n,
        [j % P for j in range(n)],
        [(j * j + 7 * j + 12345) % P for j in range(n)],
    ]


def run_oracle(oracle: str, op: str, n: int, lines: list[str]) -> list[list[int]]:
    """Feed lines to the oracle with --check; return its computed outputs."""
    proc = subprocess.run(
        [oracle, "--op", op, "--n", str(n), "--check"],
        input="\n".join(lines) + "\n",
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        print(f"FAIL: oracle --op {op} --n {n} exited {proc.returncode}")
        sys.stderr.write(proc.stderr)
        sys.exit(1)
    return [
        [int(v) for v in line.split(":")[1].split()]
        for line in proc.stdout.strip().splitlines()
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True, help="path to p3_oracle binary")
    args = parser.parse_args()

    for n in SIZES:
        vecs = crafted(n)
        ntt_py = [ntt(xs, n) for xs in vecs]
        intt_py = [intt(xs, n) for xs in vecs]

        fwd_lines = [
            " ".join(map(str, xs)) + " : " + " ".join(map(str, ys))
            for xs, ys in zip(vecs, ntt_py)
        ]
        fwd_p3 = run_oracle(args.oracle, "ntt", n, fwd_lines)
        assert fwd_p3 == ntt_py, f"ntt n={n}: oracle stdout != python"

        inv_lines = [
            " ".join(map(str, xs)) + " : " + " ".join(map(str, ys))
            for xs, ys in zip(vecs, intt_py)
        ]
        inv_p3 = run_oracle(args.oracle, "intt", n, inv_lines)
        assert inv_p3 == intt_py, f"intt n={n}: oracle stdout != python"

        rt_lines = [" ".join(map(str, ys)) for ys in ntt_py]
        roundtrip = run_oracle(args.oracle, "intt", n, rt_lines)
        assert roundtrip == vecs, f"round-trip n={n}: intt(ntt(x)) != x"

        print(f"  n={n}: {len(vecs)} vectors — ntt, intt, round-trip OK")

    print(f"PASS: Python and Plonky3 references agree at sizes {SIZES}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
