import TRZK.MatrixExpr

namespace TRZK

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
