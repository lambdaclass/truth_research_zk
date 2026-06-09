import TRZK.MatrixLowerLoop

open TRZK

/-! Tests for the loop-shaped lowering `MatrixExpr.lowerLoop` (task 5.1):
    each matrix primitive produces the expected `LoopExpr` shape. -/

/-- Strip the top-level `temp` wrapper `lowerLoop` adds, exposing the nest. -/
private def innerOf (p : LoopProgram) : LoopExpr :=
  match p.body with
  | .temp _ inner => inner
  | other         => other

/-! ## var_matrix: a bare input lowers to the empty nest (inputs already in
    `mem`), arity = m·n, result region at base 0. -/

#guard
  match (MatrixExpr.var_matrix 0 (2, 3)).lowerLoop with
  | some p => p.arity == 6 && p.outBase == 0 && p.outSize == 6 &&
              innerOf p == .nop && p.tables.isEmpty
  | none => false

/-! ## const_matrix: one scalar write per cell, no loops, arity 0. -/

#guard
  match (MatrixExpr.const_matrix (2, 2) [1, 2, 3, 4]).lowerLoop with
  | some p => p.arity == 0 && p.outSize == 4 && (innerOf p).usedVars.isEmpty
  | none => false

/-! ## matmul: a 3-deep loop nest (row, col, contraction) over three fresh
    loop vars, no twiddle tables. -/

#guard
  match (MatrixExpr.matmul (.var_matrix 0 (2, 2)) (.var_matrix 1 (2, 2))).lowerLoop with
  | some p =>
      p.arity == 8 && p.outSize == 4 && p.tables.isEmpty &&
      -- three distinct loop variables bound somewhere in the nest.
      (innerOf p).usedVars.eraseDups.length == 3
  | none => false

/-! ## transpose: a 2-deep nest (result row, col), no contraction, no tables. -/

#guard
  match (MatrixExpr.transpose (.var_matrix 0 (2, 3))).lowerLoop with
  | some p =>
      p.arity == 6 && p.outSize == 6 && p.tables.isEmpty &&
      (innerOf p).usedVars.eraseDups.length == 2
  | none => false

/-! ## ntt: a 2-deep nest (output k, input j) plus exactly one twiddle table
    named `_twiddles_{n}` of `n²` entries. -/

private def ntt8 : MatrixExpr := .ntt 8 ⟨1⟩ (.var_matrix 0 (1, 8))

#guard
  match ntt8.lowerLoop with
  | some p =>
      p.arity == 8 && p.outSize == 8 &&
      p.tables.length == 1 &&
      p.tables[0]!.name == "_twiddles_8" &&
      p.tables[0]!.values.size == 64 &&
      (innerOf p).usedVars.eraseDups.length == 2
  | none => false

/-! ## intt: its own table `_intt_twiddles_{n}`, distinct from the forward one
    (it bakes the n⁻¹ normalisation). -/

#guard
  match (MatrixExpr.intt 8 ⟨1⟩ (.var_matrix 0 (1, 8))).lowerLoop with
  | some p => p.tables.length == 1 && p.tables[0]!.name == "_intt_twiddles_8"
  | none => false

/-! ## Shape-inconsistent input lowers to none. -/

#guard ((MatrixExpr.matmul (.var_matrix 0 (2, 3)) (.var_matrix 1 (4, 5))).lowerLoop).isNone

/-! ## Distinct matrix variables get distinct input regions; arity sums them. -/

#guard
  match (MatrixExpr.matmul (.var_matrix 0 (1, 2)) (.var_matrix 1 (2, 3))).lowerLoop with
  | some p => p.arity == 8 && p.outSize == 3   -- (1×2)·(2×3) ⇒ 1×3
  | none => false
