import TRZK.MatrixExpr
import TRZK.MatrixLower
import TRZK.LoopExpr
import TRZK.Program

namespace TRZK

/-! # Loop-shaped lowering: `MatrixExpr → LoopExpr`

    The codegen lowering target. Replaces the placeholder per-cell
    `MatrixExpr.lower row col` (which unrolled each output element into a flat
    `ArithExpr`); the dense `materialize` it built on stays as the structural
    reference and the cost-oracle / round-trip tests still use it.

    ## Memory model

    A single flat scalar memory `mem` holds inputs, intermediates, and the
    output at distinct contiguous offsets (row-major within each region). The
    matrix-variable inputs occupy `[0, arity)` exactly as `materialize`
    allocates them, so the emitted ABI is unchanged: positional `x0..x(arity-1)`
    seed `mem[0..arity)`, the body runs, and the result region is returned as
    `[u32; m·n]`.

    `lower` returns a `LoopProgram`: the body, the input arity, the result
    region (base offset and `m·n` size), the high-water memory size, and any
    twiddle `ConstTable`s the NTT introduced. `LoopProgram` itself lives in
    `TRZK.LoopExpr` so the emitter can consume it without importing this file. -/

/-- Lowering state: the matrix-variable base map (shared with `materialize`'s
    allocation so a variable seen twice resolves to the same `mem` region),
    the high-water mark for fresh region allocation, a fresh loop-variable
    counter, and the twiddle tables accumulated so far. -/
private structure LoopState where
  vbases   : Std.HashMap Nat Nat := ∅
  /-- High-water mark: next free `mem` offset. Starts past the input region. -/
  hwm      : Nat := 0
  /-- Next fresh loop-variable index. -/
  nextVar  : Nat := 0
  tables   : List ConstTable := []
  deriving Inhabited

/-- Resolve the `mem` region base of matrix variable `vi`. The input region
    `[0, arity)` is pre-allocated (`seedVars` below) so every variable already
    has a base; this only looks it up. -/
private def LoopState.varBase (st : LoopState) (vi : Nat) : Nat :=
  st.vbases.getD vi 0

/-- Allocate a fresh `count`-cell region past the high-water mark. -/
private def LoopState.allocRegion (st : LoopState) (count : Nat) :
    Nat × LoopState :=
  (st.hwm, { st with hwm := st.hwm + count })

/-- Take a fresh loop-variable index. -/
private def LoopState.freshVar (st : LoopState) : Nat × LoopState :=
  (st.nextVar, { st with nextVar := st.nextVar + 1 })

/-- `_twiddles_{n}` / `_intt_twiddles_{n}`: the `n×n` row-major table whose
    entry `[k·n + j]` is the twiddle multiplying input `j` into output `k`.

    Folding the non-affine `(j·k) mod n` exponent into the table *contents* at
    elaboration time keeps the runtime index `k·n + j` affine (design D4): the
    loop nest reads `TABLE[k·n + j]`, an affine function of the two loop vars,
    and the `ω` power lives in the constant. Forward bakes `ω^(j·k)`; inverse
    bakes `n⁻¹ · ω^(-j·k)` so a single load carries both the inverse root and
    the `n⁻¹` normalisation (the two tables are distinct). -/
private def twiddleTable (n : Nat) (ω : BabyBear .canonical) : ConstTable :=
  let vals := (List.range n).flatMap fun k =>
    (List.range n).map fun j => BabyBear.toNat (BabyBear.powNat ω (j * k))
  { name := s!"_twiddles_{n}", elemTy := .u32, values := vals.toArray }

private def inttTwiddleTable (n : Nat) (ω : BabyBear .canonical) : ConstTable :=
  let ωInv : BabyBear .canonical := ⟨ω.val⁻¹⟩
  let nInv : BabyBear .canonical := ⟨(n : ZMod BabyBear.p)⁻¹⟩
  let vals := (List.range n).flatMap fun k =>
    (List.range n).map fun j =>
      BabyBear.toNat (nInv * BabyBear.powNat ωInv (j * k))
  { name := s!"_intt_twiddles_{n}", elemTy := .u32, values := vals.toArray }

/-- Pre-allocate the input region: walk `e` left-to-right (the order
    `materialize` and `lowerAux` both use) assigning each distinct matrix
    variable a contiguous `[base, base + m·n)` slice of `mem` starting at 0.
    Returns the seeded `vbases` map and the arity (= high-water after inputs).
    Seeding up front guarantees intermediates and constants (allocated past
    the high-water mark) never collide with the input region the emitted ABI
    seeds from `x0..`. -/
private partial def seedVars : MatrixExpr → Std.HashMap Nat Nat × Nat →
    Std.HashMap Nat Nat × Nat
  | .var_matrix vi (m, n), (map, hwm) =>
      if map.contains vi then (map, hwm)
      else (map.insert vi hwm, hwm + m * n)
  | .const_matrix _ _, acc => acc
  | .matmul a b, acc       => seedVars b (seedVars a acc)
  | .transpose a, acc      => seedVars a acc
  | .ntt _ _ a, acc        => seedVars a acc
  | .intt _ _ a, acc       => seedVars a acc

/-- Row-major flat index `r·cols + c` as an affine `IdxExpr` over loop vars
    `vr` (row) and `vc` (col), offset by region `base`:
    `base + cols·i{vr} + i{vc}`. -/
private def rowMajorIdx (base cols vr vc : Nat) : IdxExpr :=
  .add (.affine base cols vr) (.var vc)

/-- Lower `e` so its result lands in a fresh `mem` region; return that region's
    base offset, the loop body computing it, and the updated state. Variables
    and constants are leaves; `matmul`/`transpose`/`ntt`/`intt` emit loop nests
    reading their already-lowered operands. -/
private partial def lowerAux (e : MatrixExpr) (st : LoopState) :
    Option (Nat × LoopExpr × LoopState) := do
  let (m, n) ← e.shape
  match e with
  | .var_matrix vi _ =>
      -- Inputs already live in `mem` at a pre-seeded base; no body.
      some (st.varBase vi, .nop, st)
  | .const_matrix _ entries =>
      let (base, st1) := st.allocRegion (m * n)
      let arr := entries.toArray
      -- One scalar write per cell: mem[base + i] = entries[i].
      let body := (List.range (m * n)).foldl (init := .nop) fun acc i =>
        let w : LoopExpr := .compute (.const arr[i]!) [] (.const (base + i)) false
        match acc with | .nop => w | _ => .seq acc w
      some (base, body, st1)
  | .transpose a => do
      let (baseA, bodyA, st1) ← lowerAux a st
      let (ma, na) ← a.shape           -- result (m,n) = (na, ma)
      let (base, st2) := st1.allocRegion (m * n)
      let (vr, st3) := st2.freshVar     -- row of result in [0, n) = [0, ma)
      let (vc, st4) := st3.freshVar     -- col of result in [0, m) = [0, na)
      -- out[vr][vc] = A[vc][vr]; result is (na, ma), so out cols = ma.
      let writeIdx := rowMajorIdx base ma vr vc
      let readIdx  := rowMajorIdx baseA na vc vr
      let cell : LoopExpr :=
        .compute (.var 0) [(.mem, readIdx)] writeIdx false
      let nest : LoopExpr := .for' vr 0 na (.for' vc 0 ma cell)
      some (base, seqNop bodyA nest, st4)
  | .matmul a b => do
      let (baseA, bodyA, st1) ← lowerAux a st
      let (baseB, bodyB, st2) ← lowerAux b st1
      let (ma, k) ← a.shape
      let (_,  nb) ← b.shape
      let (base, st3) := st2.allocRegion (m * n)
      let (vr, st4) := st3.freshVar     -- result row in [0, m)
      let (vc, st5) := st4.freshVar     -- result col in [0, n)
      let (vi, st6) := st5.freshVar     -- contraction index in [0, k)
      let outIdx := rowMajorIdx base n vr vc
      -- mem[out] = 0
      let zero : LoopExpr := .compute (.const 0) [] outIdx false
      -- mem[out] += A[vr][vi] * B[vi][vc]
      let aIdx := rowMajorIdx baseA k vr vi
      let bIdx := rowMajorIdx baseB nb vi vc
      let mac : LoopExpr :=
        .compute (.mul (.var 0) (.var 1)) [(.mem, aIdx), (.mem, bIdx)] outIdx true
      let inner : LoopExpr := .seq zero (.for' vi 0 k mac)
      let nest : LoopExpr := .for' vr 0 ma (.for' vc 0 nb inner)
      some (base, seqNop (seqNop bodyA bodyB) nest, st6)
  | .ntt nn ω a =>
      lowerTransform a st nn (twiddleTable nn ω)
  | .intt nn ω a =>
      lowerTransform a st nn (inttTwiddleTable nn ω)
where
  /-- Sequence two bodies, dropping `nop` operands so leaf inputs don't litter
      the tree with empty statements. -/
  seqNop : LoopExpr → LoopExpr → LoopExpr
    | .nop, b => b
    | a, .nop => a
    | a, b    => .seq a b
  /-- Shared NTT/iNTT lowering: `for k { out[k]=0; for j { out[k] += x[j] ·
      TABLE[k·n+j] } }`, reading the row vector `a` and the precomputed
      twiddle `table`. Registers `table` in state. -/
  lowerTransform (a : MatrixExpr) (st : LoopState) (nn : Nat)
      (table : ConstTable) : Option (Nat × LoopExpr × LoopState) := do
    let (baseA, bodyA, st1) ← lowerAux a st
    let st2 := { st1 with tables := st1.tables ++ [table] }
    let (base, st3) := st2.allocRegion nn        -- result is 1 × n
    let (vk, st4) := st3.freshVar
    let (vj, st5) := st4.freshVar
    let outIdx : IdxExpr := .add (.const base) (.var vk)
    let zero : LoopExpr := .compute (.const 0) [] outIdx false
    let xIdx : IdxExpr := .add (.const baseA) (.var vj)
    let twIdx : IdxExpr := .add (.mul nn (.var vk)) (.var vj)   -- k·n + j
    let mac : LoopExpr :=
      .compute (.mul (.var 0) (.var 1))
        [(.mem, xIdx), (.table table.name, twIdx)] outIdx true
    let inner : LoopExpr := .seq zero (.for' vj 0 nn mac)
    let nest : LoopExpr := .for' vk 0 nn inner
    some (base, seqNop bodyA nest, st5)

/-- Lower a matrix expression to a loop-shaped `LoopProgram` over flat `mem`.
    Returns `none` for shape-inconsistent inputs. The result region is the
    top-level expression's region; the emitter returns it as `[u32; m·n]`. -/
def MatrixExpr.lowerLoop (e : MatrixExpr) : Option LoopProgram := do
  let (m, n) ← e.shape
  let (vbases, arity) := seedVars e (∅, 0)
  let (outBase, inner, st) ← lowerAux e { vbases, hwm := arity }
  -- `temp` declares the flat scratch buffer holding inputs, intermediates, and
  -- the output; the loop nest runs inside its scope. This is the buffer the
  -- emitter realizes as `mem` and the constructor the spec's 5-set requires.
  let body : LoopExpr := .temp st.hwm inner
  some { arity, memSize := st.hwm, outBase, outSize := m * n, tables := st.tables, body }

end TRZK
