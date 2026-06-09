import TRZK.LoopExpr
import TRZK.Emit

open TRZK

/-! Tests for the loop IR (task 1.4) and per-constructor emission (task 5.2). -/

/-! ## IdxExpr evaluation. -/

#guard (IdxExpr.const 7).eval (fun _ => 0) == 7
#guard (IdxExpr.var 1).eval (fun i => i * 10) == 10
-- affine base stride v = base + stride·env v.
#guard (IdxExpr.affine 3 4 0).eval (fun _ => 5) == 23
#guard (IdxExpr.add (.var 0) (.const 1)).eval (fun _ => 9) == 10
#guard (IdxExpr.mul 3 (.var 0)).eval (fun _ => 4) == 12
-- Row-major k·n + j at n = 8, k = 2, j = 3 ⇒ 19.
#guard (IdxExpr.add (.mul 8 (.var 0)) (.var 1)).eval
         (fun i => [2, 3].toArray[i]!) == 19

/-! ## LoopExpr.size and usedVars on representative shapes. -/

private def matmulCell : LoopExpr :=
  .compute (.mul (.var 0) (.var 1))
    [(.mem, .var 0), (.mem, .var 1)] (.var 2) true

-- A 3-deep nest with a seq inside: size counts structural nodes (compute = 1).
private def nest : LoopExpr :=
  .for' 0 0 2 1 (.for' 1 0 2 1 (.seq (.compute (.const 0) [] (.var 0) false)
                                     (.for' 2 0 2 1 matmulCell)))

#guard nest.size == 6        -- for, for, seq, compute, for, compute
#guard nest.usedVars == [0, 1, 2]
#guard LoopExpr.nop.size == 1
#guard LoopExpr.nop.usedVars == ([] : List Nat)
#guard (LoopExpr.temp 16 nest).usedVars == [0, 1, 2]
#guard (LoopExpr.seq .nop matmulCell).size == 3

/-! ## BEq / construction. -/

#guard (matmulCell == matmulCell) == true
#guard (matmulCell == .compute (.mul (.var 0) (.var 1))
          [(.mem, .var 0), (.mem, .var 1)] (.var 2) false) == false
#guard (BufRef.mem == BufRef.table "_t") == false
#guard (BufRef.table "_t" == BufRef.table "_t") == true

/-! ## Index emission (task 5.2). -/

#guard emitIdx (.const 5) == "5"
#guard emitIdx (.var 3) == "i3"
#guard emitIdx (.affine 4 2 0) == "4 + 2 * i0"
#guard emitIdx (.affine 0 2 0) == "2 * i0"
#guard emitIdx (.add (.affine 4 2 0) (.var 1)) == "4 + 2 * i0 + i1"
#guard emitIdx (.add (.mul 8 (.var 0)) (.var 1)) == "8 * i0 + i1"

/-! ## Gather emission. -/

#guard emitGather (.mem, .var 0) == "mem[i0]"
#guard emitGather (.table "_twiddles_8", .add (.mul 8 (.var 0)) (.var 1)) ==
  "_twiddles_8[8 * i0 + i1]"

/-! ## Kernel emission: `.var j` resolves to gather lane j. -/

#guard emitKernel [(.mem, .var 0), (.mem, .var 1)] (.mul (.var 0) (.var 1)) ==
  "bb_mul(mem[i0], mem[i1])"
#guard emitKernel [(.table "_t", .var 0)] (.var 0) == "_t[i0]"
#guard emitKernel [] (.const 0) == "0u32"

/-! ## Per-constructor LoopExpr emission (task 5.2). -/

-- `nop` emits nothing (task 3.6).
#guard emitLoop "" .nop == ""

-- `compute` non-accumulating is a plain write; accumulating folds via bb_add
-- (task 3.4).
#guard emitLoop "" (.compute (.const 0) [] (.var 0) false) == "mem[i0] = 0u32;"
#guard emitLoop "" matmulCell ==
  "mem[i2] = bb_add(mem[i2], bb_mul(mem[i0], mem[i1]));"

-- `for'` wraps the body in a Rust range loop (task 3.2); unit stride stays a
-- bare range.
#guard emitLoop "" (.for' 0 0 4 1 (.compute (.const 1) [] (.var 0) false)) ==
  "for i0 in 0..4 {\n    mem[i0] = 1u32;\n}"

-- A non-unit stride emits `.step_by`, leaving the index expression free of a
-- synthetic multiply (the unroller advances the counter, not the address).
#guard emitLoop "" (.for' 0 0 8 4 (.compute (.const 1) [] (.var 0) false)) ==
  "for i0 in (0..8).step_by(4) {\n    mem[i0] = 1u32;\n}"

-- `seq` emits both bodies in order (task 3.3).
#guard emitLoop "" (.seq (.compute (.const 1) [] (.const 0) false)
                         (.compute (.const 2) [] (.const 1) false)) ==
  "mem[0] = 1u32;\nmem[1] = 2u32;"

-- `temp` declares a stack buffer scoping the body (task 3.5).
#guard
  ((emitLoop "" (.temp 4 (.compute (.const 0) [] (.const 0) false))).splitOn
    "let mut mem: [u32; 4] = [0u32; 4];").length == 2
