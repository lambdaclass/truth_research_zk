import LambdaSat
import TRZK.ArithExpr

open LambdaSat UnionFind

namespace TRZK

/-- E-graph node type. Children are `EClassId`s rather than subterms.
    Mirrors `ArithExpr`: canonical BabyBear constants, canonical arithmetic,
    Montgomery-domain multiplication, and explicit conversion ops. -/
inductive ArithOp where
  | const    : BabyBear .canonical → ArithOp
  | var      : Nat → ArithOp
  | add      : EClassId → EClassId → ArithOp
  | sub      : EClassId → EClassId → ArithOp
  | neg      : EClassId → ArithOp
  | mul      : EClassId → EClassId → ArithOp
  | montMul  : EClassId → EClassId → ArithOp
  | toMont   : EClassId → ArithOp
  | fromMont : EClassId → ArithOp
  deriving Repr, Inhabited, DecidableEq

instance : BEq ArithOp where
  beq a b := decide (a = b)

instance : Hashable ArithOp where
  hash
    | .const n     => mixHash 1 (hash n)
    | .var i       => mixHash 2 (hash i)
    | .add l r     => mixHash 3 (mixHash (hash l) (hash r))
    | .sub l r     => mixHash 4 (mixHash (hash l) (hash r))
    | .neg c       => mixHash 5 (hash c)
    | .mul l r     => mixHash 6 (mixHash (hash l) (hash r))
    | .montMul l r => mixHash 7 (mixHash (hash l) (hash r))
    | .toMont c    => mixHash 8 (hash c)
    | .fromMont c  => mixHash 9 (hash c)

instance : LawfulBEq ArithOp where
  eq_of_beq {a b} h := by simp [BEq.beq] at h; exact h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable ArithOp where
  hash_eq {a b} h := by
    have := eq_of_beq h; subst this; rfl

/-- Per-op local cost. Not hardware-calibrated; chosen so the qualitative
    extraction behaviour matches the design's intent:
    - A single `mul` is kept canonical (conversion cost outweighs Montgomery
      savings).
    - A chain of three or more `mul`s prefers Montgomery (savings amortise
      the conversion overhead).
    With the current weights, a k-chain of canonical muls costs `8k`; the
    saturated Montgomery realisation costs `k · 1 + (k+1) · 4 + 4 = 5k + 8`.
    Crossover is at k = 3. -/
def ArithOp.localCost : ArithOp → Nat
  | .const _     => 0
  | .var _       => 0
  | .add _ _     => 1
  | .sub _ _     => 1
  | .neg _       => 1
  | .mul _ _     => 8
  | .montMul _ _ => 1
  | .toMont _    => 4
  | .fromMont _  => 4

instance : NodeOps ArithOp where
  children
    | .const _     => []
    | .var _       => []
    | .add l r     => [l, r]
    | .sub l r     => [l, r]
    | .neg c       => [c]
    | .mul l r     => [l, r]
    | .montMul l r => [l, r]
    | .toMont c    => [c]
    | .fromMont c  => [c]
  mapChildren f
    | .const n     => .const n
    | .var i       => .var i
    | .add l r     => .add (f l) (f r)
    | .sub l r     => .sub (f l) (f r)
    | .neg c       => .neg (f c)
    | .mul l r     => .mul (f l) (f r)
    | .montMul l r => .montMul (f l) (f r)
    | .toMont c    => .toMont (f c)
    | .fromMont c  => .fromMont (f c)
  replaceChildren op cs :=
    match op, cs with
    | .add _ _,     [l, r] => .add l r
    | .sub _ _,     [l, r] => .sub l r
    | .neg _,       [c]    => .neg c
    | .mul _ _,     [l, r] => .mul l r
    | .montMul _ _, [l, r] => .montMul l r
    | .toMont _,    [c]    => .toMont c
    | .fromMont _,  [c]    => .fromMont c
    | op, _ => op
  localCost := ArithOp.localCost
  mapChildren_children f op := by cases op <;> simp
  mapChildren_id op := by cases op <;> simp
  replaceChildren_children op ids hlen := by
    cases op with
    | const _     => simp at hlen; simp [hlen]
    | var _       => simp at hlen; simp [hlen]
    | add _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | sub _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | neg _       =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | mul _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | montMul _ _ =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | toMont _    =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | fromMont _  =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
  replaceChildren_sameShape op ids hlen := by
    cases op with
    | const _     => simp at hlen; simp
    | var _       => simp at hlen; simp
    | add _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | sub _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | neg _       =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | mul _ _     =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | montMul _ _ =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | toMont _    =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp
    | fromMont _  =>
      simp at hlen
      match ids, hlen with
      | [_], _ => simp

instance : Extractable ArithOp ArithExpr where
  reconstruct op childExprs :=
    match op, childExprs with
    | .const n,     []     => some (.const n)
    | .var i,       []     => some (.var i)
    | .add _ _,     [l, r] => some (.add l r)
    | .sub _ _,     [l, r] => some (.sub l r)
    | .neg _,       [c]    => some (.neg c)
    | .mul _ _,     [l, r] => some (.mul l r)
    | .montMul _ _, [l, r] => some (.montMul l r)
    | .toMont _,    [c]    => some (.toMont c)
    | .fromMont _,  [c]    => some (.fromMont c)
    | _, _                 => none

end TRZK
