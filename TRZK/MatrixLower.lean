import TRZK.MatrixExpr

namespace TRZK

/-- Fast exponentiation in `BabyBear .canonical` (square-and-multiply).
    Used at materialize time to precompute twiddle constants `ω^k mod p`
    baked into the lowered scalar program. Linear recursion would overflow
    the stack for the exponents naive NTT reaches at `n = 256` (`j·k` up
    to 65 025). -/
def BabyBear.powNat (a : BabyBear .canonical) (k : Nat) :
    BabyBear .canonical :=
  if k = 0 then ⟨1⟩
  else
    let half := BabyBear.powNat a (k / 2)
    let sq := half * half
    if k % 2 = 0 then sq else sq * a
  termination_by k

/-- Twiddle row `[ω^(j·k) | k < n]` for fixed `j`. -/
private def twiddleRow (n : Nat) (ω : BabyBear .canonical) (j : Nat) :
    Array (BabyBear .canonical) :=
  (List.range n).toArray.map fun k => BabyBear.powNat ω (j * k)

/-- Per-cell scalar expression for `(ntt n ω x)[0][k]` given the materialized
    grid `gx` of `x` (a 1×n row vector). Builds the dot-product
    `Σⱼ gx[0][j] · ω^(j·k)` as an `ArithExpr.add`-folded chain with
    twiddles baked as `.const` leaves. -/
private def nttCell (n : Nat) (ω : BabyBear .canonical)
    (gx : Array (Array ArithExpr)) (k : Nat) : ArithExpr :=
  let row := gx[0]!
  (List.range n).foldl
    (init := .const 0)
    (fun acc j =>
      let t : BabyBear .canonical := BabyBear.powNat ω (j * k)
      .add acc (.mul row[j]! (.const t)))

/-- Per-cell scalar expression for `(intt n ω x)[0][k]` given the materialized
    grid `gx`. iNTT bakes `(1/n) · ω^(-j·k)` into each twiddle, so a single
    constant per `(j, k)` pair carries both the inverse-root power and the
    `n⁻¹` normalisation. -/
private def inttCell (n : Nat) (ω : BabyBear .canonical)
    (gx : Array (Array ArithExpr)) (k : Nat) : ArithExpr :=
  let row := gx[0]!
  let ωInv : BabyBear .canonical := ⟨ω.val⁻¹⟩
  let nInv : BabyBear .canonical := ⟨(n : ZMod BabyBear.p)⁻¹⟩
  (List.range n).foldl
    (init := .const 0)
    (fun acc j =>
      let tBase : BabyBear .canonical := BabyBear.powNat ωInv (j * k)
      let t : BabyBear .canonical := nInv * tBase
      .add acc (.mul row[j]! (.const t)))

/-- Dense row-major grid of scalar expressions. `rows.size = m`, every row
    has `n` entries; well-formedness is enforced by `materialize`. -/
abbrev MatrixGrid := Array (Array ArithExpr)

private structure LowerState where
  /-- Maps a `var_matrix` index to the base `ArithExpr.var` index allocated
      to its row-major flattening. A single matrix variable seen twice in
      the surface AST resolves to the same base. -/
  vbases : Std.HashMap Nat Nat := ∅
  /-- Total scalar-var slots allocated so far. -/
  arity  : Nat := 0
  deriving Inhabited

private def LowerState.alloc (st : LowerState) (vi : Nat) (count : Nat) :
    Nat × LowerState :=
  match st.vbases[vi]? with
  | some base => (base, st)
  | none =>
    let base := st.arity
    (base, { vbases := st.vbases.insert vi base, arity := st.arity + count })

/-- Materialize a `MatrixExpr` to a dense grid of `ArithExpr` cells, also
    returning the total scalar arity allocated for matrix variables. The
    grid is `none` iff the surface expression is shape-inconsistent. -/
partial def materializeAux : MatrixExpr → LowerState →
    Option (MatrixGrid × LowerState)
  | .const_matrix (m, n) entries, st => do
      guard (entries.length = m * n)
      let arr := entries.toArray.map ArithExpr.const
      let rows := (List.range m).toArray.map fun r =>
        (List.range n).toArray.map fun c => arr[r * n + c]!
      some (rows, st)
  | .var_matrix vi (m, n), st =>
      let (base, st') := st.alloc vi (m * n)
      let rows := (List.range m).toArray.map fun r =>
        (List.range n).toArray.map fun c => .var (base + r * n + c)
      some (rows, st')
  | .matmul a b, st => do
      let (ga, st1) ← materializeAux a st
      let (gb, st2) ← materializeAux b st1
      let m := ga.size
      guard (m > 0)
      let k := ga[0]!.size
      guard (gb.size = k)
      let n := if k = 0 then 0 else gb[0]!.size
      guard (ga.all (·.size = k))
      guard (gb.all (·.size = n))
      let rows := (List.range m).toArray.map fun r =>
        (List.range n).toArray.map fun c =>
          -- sum over i: a[r][i] * b[i][c]; fold left, seeded with const 0.
          (List.range k).foldl
            (init := .const 0)
            (fun acc i => .add acc (.mul ga[r]![i]! gb[i]![c]!))
      some (rows, st2)
  | .transpose a, st => do
      let (ga, st1) ← materializeAux a st
      let m := ga.size
      let n := if m = 0 then 0 else ga[0]!.size
      let rows := (List.range n).toArray.map fun r =>
        (List.range m).toArray.map fun c => ga[c]![r]!
      some (rows, st1)
  | .ntt n ω a, st => do
      let (ga, st1) ← materializeAux a st
      guard (ga.size = 1)
      guard (ga[0]!.size = n)
      let row := (List.range n).toArray.map fun k => nttCell n ω ga k
      some (#[row], st1)
  | .intt n ω a, st => do
      let (ga, st1) ← materializeAux a st
      guard (ga.size = 1)
      guard (ga[0]!.size = n)
      let row := (List.range n).toArray.map fun k => inttCell n ω ga k
      some (#[row], st1)

/-- Materialize a matrix expression into its dense grid of scalar
    expressions. Returns `none` for shape-inconsistent inputs. -/
def MatrixExpr.materialize (e : MatrixExpr) : Option (MatrixGrid × Nat) :=
  (materializeAux e {}).map fun (g, st) => (g, st.arity)

/-- Lower a matrix expression to the scalar expression for one output cell,
    plus the total scalar arity used for matrix-variable inputs. Out-of-bounds
    indices and shape-inconsistent inputs return `none`. -/
def MatrixExpr.lower (e : MatrixExpr) (row col : Nat) :
    Option (ArithExpr × Nat) := do
  let (grid, arity) ← e.materialize
  guard (row < grid.size)
  let r := grid[row]!
  guard (col < r.size)
  some (r[col]!, arity)

end TRZK
