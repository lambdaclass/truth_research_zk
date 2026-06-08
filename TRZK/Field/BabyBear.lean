import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

namespace TRZK

/-- Field-value representation tag. A `BabyBear .canonical` is a residue in
    `[0, p)`; a `BabyBear .montgomery` stores `x · R mod p` for the field
    element `x`. Arithmetic on `+`, `-`, unary `-` is bit-identical across
    representations (linear in `x`); `*` differs (Montgomery requires REDC). -/
inductive FieldRepr where
  | canonical
  | montgomery
  deriving DecidableEq, Repr, BEq, Hashable, Inhabited

/-- BabyBear prime: `p = 2³¹ − 2²⁷ + 1 = 2013265921`. -/
abbrev BabyBear.p : Nat := 2013265921

/-- Primality of the BabyBear prime.

    `native_decide` compiles the decision procedure to native code and trusts
    the result, bypassing the kernel reducer. This adds the compiler and
    native runtime to the trusted computing base for this theorem. The
    alternative — `decide` or `norm_num` — produces a kernel proof term that
    triggers a deep-recursion failure on this prime. Revisit if a kernel-only
    primality certificate becomes practical for primes of this size. -/
theorem BabyBear.p_prime : Nat.Prime BabyBear.p := by native_decide

instance : Fact (Nat.Prime BabyBear.p) := ⟨BabyBear.p_prime⟩

/-- BabyBear field element, tagged by representation.

    The same `ZMod p` value means *different field elements* in canonical vs
    Montgomery encoding: canonical `val` denotes `val`; Montgomery `val`
    denotes `val · R⁻¹ mod p`. Conversions live as `toMont` / `fromMont` and
    as first-class e-graph ops (`to_mont`, `from_mont`). -/
structure BabyBear (r : FieldRepr) where
  val : ZMod BabyBear.p
  deriving DecidableEq

namespace BabyBear

/-- Montgomery radix: `R = 2³² mod p`. The smallest power of two larger than
    `p` makes REDC cheap (the division-by-R becomes a 32-bit shift). -/
def R : ZMod p := (2 ^ 32 : ZMod p)

/-- `R²` precomputed for the `toMont` round-trip via REDC. -/
def R_squared : ZMod p := R * R

variable {r : FieldRepr}

instance : Inhabited (BabyBear r) := ⟨⟨0⟩⟩
instance : Repr (BabyBear r) := ⟨fun a _ => repr a.val⟩
instance : BEq (BabyBear r) := ⟨fun a b => decide (a.val = b.val)⟩

instance : LawfulBEq (BabyBear r) where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp [BEq.beq] at h
    exact congrArg BabyBear.mk h
  rfl {a} := by simp [BEq.beq]

/-- Hash via the underlying `Fin p` value of `ZMod p`. -/
instance : Hashable (BabyBear r) where
  hash a := hash (ZMod.val a.val)

instance : LawfulHashable (BabyBear r) where
  hash_eq {a b} h := by
    have := eq_of_beq h; subst this; rfl

/-- Construct from a `Nat` literal, reducing mod `p`. The result lives in the
    canonical residue range `[0, p)`. For a Montgomery-encoded literal, lift
    via `toMont` or via the `to_mont` e-graph op. -/
def ofNat (n : Nat) (r : FieldRepr := .canonical) : BabyBear r := ⟨(n : ZMod p)⟩

instance {r : FieldRepr} {n : Nat} : OfNat (BabyBear r) n := ⟨ofNat n r⟩

/-- Underlying `Nat` residue in `[0, p)`. The interpretation depends on `r`:
    for `.canonical`, it is the field-element residue; for `.montgomery`, it
    is the Montgomery-encoded representation. -/
def toNat (a : BabyBear r) : Nat := ZMod.val a.val

/-- Algebraic instances lifted from `ZMod p`. Addition, subtraction, and
    negation are repr-polymorphic: `(x·R) + (y·R) = (x+y)·R`, so the same
    `ZMod p` operation works on canonical and Montgomery encodings alike.

    Multiplication is **only** lifted for canonical: Montgomery multiplication
    requires REDC and lives as `montMul` (and `mont_mul` in the e-graph). -/
instance : Add (BabyBear r) := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub (BabyBear r) := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Neg (BabyBear r) := ⟨fun a => ⟨-a.val⟩⟩
instance : Mul (BabyBear .canonical) := ⟨fun a b => ⟨a.val * b.val⟩⟩
instance : Zero (BabyBear r) := ⟨⟨0⟩⟩
instance : One (BabyBear .canonical) := ⟨⟨1⟩⟩

/-- Convert a canonical residue to its Montgomery encoding: `x ↦ x · R mod p`.
    Inverse of `fromMont`. -/
def toMont (a : BabyBear .canonical) : BabyBear .montgomery :=
  ⟨a.val * R⟩

/-- Convert a Montgomery encoding back to its canonical residue: `x · R ↦ x`.
    Implemented as multiplication by `R⁻¹` mod `p`. Inverse of `toMont`. -/
def fromMont (a : BabyBear .montgomery) : BabyBear .canonical :=
  ⟨a.val * R⁻¹⟩

/-- Montgomery-domain multiplication: given Montgomery encodings of `x` and
    `y` (i.e. `x·R` and `y·R`), produce the Montgomery encoding of `x·y`
    (i.e. `x·y·R`). Equal to `(x·R)·(y·R)·R⁻¹ = x·y·R`. -/
def montMul (a b : BabyBear .montgomery) : BabyBear .montgomery :=
  ⟨a.val * b.val * R⁻¹⟩

/-- Boolean check for NTT-domain sizes on BabyBear: `n = 2^k` for some
    `k ≤ 27`. Used by the smart constructor. The lemma `nttSize_iff` proves
    this is equivalent to "`n` is a power of two and `n ∣ p − 1`". -/
def isNttSize (n : Nat) : Bool :=
  (List.range 28).any (fun k => n = 2 ^ k)

/-- For BabyBear, `p − 1 = 2³¹ − 2²⁷ = 2²⁷ · 15`. The 2-adic valuation of
    `p − 1` is 27, so a power of two `n = 2ᵏ` divides `p − 1` iff `k ≤ 27`.
    `isNttSize n ↔ n.isPowerOfTwo ∧ n ∣ p − 1`. -/
theorem nttSize_iff (n : Nat) :
    BabyBear.isNttSize n = true ↔ n.isPowerOfTwo ∧ n ∣ (BabyBear.p - 1) := by
  have hp_eq : BabyBear.p - 1 = 2 ^ 27 * 15 := by decide
  constructor
  · intro h
    simp [BabyBear.isNttSize, List.any_eq_true] at h
    obtain ⟨k, hk_lt, heq⟩ := h
    refine ⟨⟨k, heq⟩, ?_⟩
    rw [heq, hp_eq]
    exact Dvd.dvd.mul_right
      ((Nat.pow_dvd_pow_iff_le_right (by decide : (1 : Nat) < 2)).mpr
        (Nat.le_of_lt_succ hk_lt)) 15
  · rintro ⟨⟨k, hk⟩, hdvd⟩
    -- From `2^k ∣ p − 1 = 2^27 · 15` and `gcd(2, 15) = 1`, deduce `k ≤ 27`.
    rw [hk, hp_eq] at hdvd
    have hcop : Nat.Coprime (2 ^ k) 15 := (by decide : Nat.Coprime 2 15).pow_left k
    have h2k_dvd : 2 ^ k ∣ 2 ^ 27 := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
    have hk_le : k ≤ 27 :=
      (Nat.pow_dvd_pow_iff_le_right (by decide : (1 : Nat) < 2)).mp h2k_dvd
    simp [BabyBear.isNttSize, List.any_eq_true]
    exact ⟨k, Nat.lt_succ_of_le hk_le, hk⟩

end BabyBear

end TRZK
