-- MatrixExpr spec: forward NTT of a length-8 BabyBear row vector.
-- The lowering bakes twiddle constants `ω^(j*k) mod p` into the scalar
-- program; the emitted Rust unrolls the n² muls + n² adds without a
-- table lookup. Output is 8 cells; input is row-major flattened.
open TRZK (MatrixExpr BabyBear)

-- Multiplicative generator of (Z/p)* for BabyBear; ω₈ = g^((p-1)/8) is a
-- primitive 8th root of unity. Kept inline so the spec is self-contained
-- and the choice of generator is local to this op.
private partial def bbPow (a : BabyBear .canonical) (k : Nat) :
    BabyBear .canonical :=
  if k = 0 then ⟨1⟩
  else
    let half := bbPow a (k / 2)
    let sq := half * half
    if k % 2 = 0 then sq else sq * a

private def gGen : BabyBear .canonical := ⟨31⟩

private def omega8 : BabyBear .canonical :=
  bbPow gGen ((BabyBear.p - 1) / 8)

def spec : MatrixExpr :=
  .ntt 8 omega8 (.var_matrix 0 (1, 8))
