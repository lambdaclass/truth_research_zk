import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

namespace TRZK

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

/-- BabyBear field element in canonical residue representation.

    The wrapper exists so that step 2 can introduce alternative representations
    (e.g. Montgomery) without rewriting every site that mentions the field type.
    Single-impl today: a thin newtype around `ZMod p`. -/
def BabyBear : Type := ZMod BabyBear.p

namespace BabyBear

instance : Field BabyBear := inferInstanceAs (Field (ZMod p))
instance : DecidableEq BabyBear := inferInstanceAs (DecidableEq (ZMod p))
instance : Repr BabyBear := inferInstanceAs (Repr (ZMod p))
instance : Inhabited BabyBear := inferInstanceAs (Inhabited (ZMod p))
instance : BEq BabyBear := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq BabyBear where
  eq_of_beq {a b} h := by simp [BEq.beq] at h; exact h
  rfl {a} := by simp [BEq.beq]

/-- Hash via the underlying `Fin p` value of `ZMod p`. -/
instance : Hashable BabyBear where
  hash a := hash (ZMod.val (a : ZMod p))

instance : LawfulHashable BabyBear where
  hash_eq {a b} h := by
    have := eq_of_beq h; subst this; rfl

/-- Construct from a `Nat` literal, reducing mod `p`. -/
def ofNat (n : Nat) : BabyBear := ((n : ZMod p) : BabyBear)

instance : OfNat BabyBear n := ⟨ofNat n⟩

/-- Canonical residue in `[0, p)` as a `Nat`. -/
def toNat (a : BabyBear) : Nat := ZMod.val (a : ZMod p)

end BabyBear

end TRZK
