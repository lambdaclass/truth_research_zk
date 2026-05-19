import LambdaSat
import TRZK.MatrixExpr

open LambdaSat UnionFind

namespace TRZK

/-- E-graph node analogue of `MatrixExpr`. Children are `EClassId`s; shapes
    and dense constants are carried by-value so they participate in node
    identity (hashcons key). -/
inductive MatrixOp where
  | const_matrix : MatrixShape → List (BabyBear .canonical) → MatrixOp
  | var_matrix   : Nat → MatrixShape → MatrixOp
  | matmul       : EClassId → EClassId → MatrixOp
  | transpose    : EClassId → MatrixOp
  deriving Repr, Inhabited, DecidableEq

instance : BEq MatrixOp where
  beq a b := decide (a = b)

instance : Hashable MatrixOp where
  hash
    | .const_matrix s es => mixHash 1 (mixHash (hash s) (hash es))
    | .var_matrix i s    => mixHash 2 (mixHash (hash i) (hash s))
    | .matmul l r        => mixHash 3 (mixHash (hash l) (hash r))
    | .transpose c       => mixHash 4 (hash c)

instance : LawfulBEq MatrixOp where
  eq_of_beq {a b} h := by simp [BEq.beq] at h; exact h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable MatrixOp where
  hash_eq {a b} h := by
    have := eq_of_beq h; subst this; rfl

/-- Per-op flat local cost. Placeholder until the field-egraph cost oracle
    lands. Leaves cost zero; `transpose` is the cheap structural op;
    `matmul` is the only contraction and dominates. -/
def MatrixOp.localCost : MatrixOp → Nat
  | .const_matrix _ _ => 0
  | .var_matrix _ _   => 0
  | .transpose _      => 1
  | .matmul _ _       => 64

instance : NodeOps MatrixOp where
  children
    | .const_matrix _ _ => []
    | .var_matrix _ _   => []
    | .matmul l r       => [l, r]
    | .transpose c      => [c]
  mapChildren f
    | .const_matrix s es => .const_matrix s es
    | .var_matrix i s    => .var_matrix i s
    | .matmul l r        => .matmul (f l) (f r)
    | .transpose c       => .transpose (f c)
  replaceChildren op cs :=
    match op, cs with
    | .matmul _ _,    [l, r] => .matmul l r
    | .transpose _,   [c]    => .transpose c
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

instance : Extractable MatrixOp MatrixExpr where
  reconstruct op childExprs :=
    match op, childExprs with
    | .const_matrix s es, []     => some (.const_matrix s es)
    | .var_matrix i s,    []     => some (.var_matrix i s)
    | .matmul _ _,        [l, r] => some (.matmul l r)
    | .transpose _,       [c]    => some (.transpose c)
    | _, _                       => none

end TRZK
