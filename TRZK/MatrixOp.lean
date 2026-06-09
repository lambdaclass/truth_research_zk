import LambdaSat
import TRZK.MatrixExpr

open LambdaSat UnionFind

namespace TRZK

/-- E-graph node analogue of `MatrixExpr`. Children are `EClassId`s; shapes
    and dense constants are carried by-value so they participate in node
    identity (hashcons key).

    `ntt` / `intt` carry the size `n` and root of unity `ω` by value; the
    rewrite engine matches by op-equality, so two NTTs with different
    `(n, ω)` are distinct nodes and the round-trip rule only fires on
    matching parameters. -/
inductive MatrixOp where
  | const_matrix : MatrixShape → List (BabyBear .canonical) → MatrixOp
  | var_matrix   : Nat → MatrixShape → MatrixOp
  | matmul       : EClassId → EClassId → MatrixOp
  | transpose    : EClassId → MatrixOp
  | ntt          : Nat → BabyBear .canonical → EClassId → MatrixOp
  | intt         : Nat → BabyBear .canonical → EClassId → MatrixOp
  | hadamard     : EClassId → EClassId → MatrixOp
  | pointwise_scalar : BabyBear .canonical → EClassId → MatrixOp
  deriving Repr, Inhabited, DecidableEq

instance : BEq MatrixOp where
  beq a b := decide (a = b)

instance : Hashable MatrixOp where
  hash
    | .const_matrix s es => mixHash 1 (mixHash (hash s) (hash es))
    | .var_matrix i s    => mixHash 2 (mixHash (hash i) (hash s))
    | .matmul l r        => mixHash 3 (mixHash (hash l) (hash r))
    | .transpose c       => mixHash 4 (hash c)
    | .ntt n ω c         => mixHash 5 (mixHash (hash n) (mixHash (hash ω) (hash c)))
    | .intt n ω c        => mixHash 6 (mixHash (hash n) (mixHash (hash ω) (hash c)))
    | .hadamard l r      => mixHash 7 (mixHash (hash l) (hash r))
    | .pointwise_scalar c x => mixHash 8 (mixHash (hash c) (hash x))

instance : LawfulBEq MatrixOp where
  eq_of_beq {a b} h := by simp [BEq.beq] at h; exact h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable MatrixOp where
  hash_eq {a b} h := by
    have := eq_of_beq h; subst this; rfl

/-- Per-op flat local cost. Fallback for nodes the field-egraph cost oracle
    cannot price (unresolvable child shapes); `MatrixPipeline.optimize`
    prices everything else through the oracle. Leaves cost zero;
    `transpose` is the cheap structural op; `matmul` and `ntt`/`intt` are
    the contraction-class ops. The naive NTT at size `n` is `n²` muls +
    `n²` adds; the cost here is a coarse quadratic-in-`n` proxy so the
    extractor distinguishes sizes. -/
def MatrixOp.localCost : MatrixOp → Nat
  | .const_matrix _ _ => 0
  | .var_matrix _ _   => 0
  | .transpose _      => 1
  | .matmul _ _       => 64
  | .ntt n _ _        => n * n
  | .intt n _ _       => n * n
  | .hadamard _ _     => 32
  | .pointwise_scalar _ _ => 16

instance : NodeOps MatrixOp where
  children
    | .const_matrix _ _ => []
    | .var_matrix _ _   => []
    | .matmul l r       => [l, r]
    | .transpose c      => [c]
    | .ntt _ _ c        => [c]
    | .intt _ _ c       => [c]
    | .hadamard l r     => [l, r]
    | .pointwise_scalar _ c => [c]
  mapChildren f
    | .const_matrix s es => .const_matrix s es
    | .var_matrix i s    => .var_matrix i s
    | .matmul l r        => .matmul (f l) (f r)
    | .transpose c       => .transpose (f c)
    | .ntt n ω c         => .ntt n ω (f c)
    | .intt n ω c        => .intt n ω (f c)
    | .hadamard l r      => .hadamard (f l) (f r)
    | .pointwise_scalar s c => .pointwise_scalar s (f c)
  replaceChildren op cs :=
    match op, cs with
    | .matmul _ _,    [l, r] => .matmul l r
    | .transpose _,   [c]    => .transpose c
    | .ntt n ω _,     [c]    => .ntt n ω c
    | .intt n ω _,    [c]    => .intt n ω c
    | .hadamard _ _,  [l, r] => .hadamard l r
    | .pointwise_scalar s _, [c] => .pointwise_scalar s c
    | op, _ => op
  localCost := MatrixOp.localCost
  mapChildren_children f op := by cases op <;> simp
  mapChildren_id op := by cases op <;> simp
  replaceChildren_children op ids hlen := by
    cases op with
    | const_matrix _ _ => simp at hlen; simp [hlen]
    | var_matrix _ _   => simp at hlen; simp [hlen]
    | matmul _ _       =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | transpose _      =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | ntt _ _ _        =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | intt _ _ _       =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | hadamard _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | pointwise_scalar _ _ =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
  replaceChildren_sameShape op ids hlen := by
    cases op with
    | const_matrix _ _ => simp at hlen; simp
    | var_matrix _ _   => simp at hlen; simp
    | matmul _ _       =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | transpose _      =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | ntt _ _ _        =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | intt _ _ _       =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | hadamard _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | pointwise_scalar _ _ =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp

instance : Extractable MatrixOp MatrixExpr where
  reconstruct op childExprs :=
    match op, childExprs with
    | .const_matrix s es, []     => some (.const_matrix s es)
    | .var_matrix i s,    []     => some (.var_matrix i s)
    | .matmul _ _,        [l, r] => some (.matmul l r)
    | .transpose _,       [c]    => some (.transpose c)
    | .ntt n ω _,         [c]    => some (.ntt n ω c)
    | .intt n ω _,        [c]    => some (.intt n ω c)
    | .hadamard _ _,      [l, r] => some (.hadamard l r)
    | .pointwise_scalar s _, [c] => some (.pointwise_scalar s c)
    | _, _                       => none

end TRZK
