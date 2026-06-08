import TRZK.ArithExpr
import TRZK.Program

namespace TRZK

/-- Affine index expression for gather/scatter addressing. The five
    constructors cover everything matmul, transpose, and the naive NTT need:
    a literal, a bare loop variable, the canonical `base + stride·iᵥ` affine
    form, and `add`/`mul` for composing nested-loop offsets (e.g. the
    row-major flattening `i·cols + j`). Symbolic table-driven indexing is out
    of scope (design D4); a later primitive can add it without disturbing
    these. Mirrors `AmoLean.Sigma.IdxExpr` from main_old. -/
inductive IdxExpr where
  | const  : Nat → IdxExpr
  | var    : Nat → IdxExpr
  | affine : (base stride : Nat) → (v : Nat) → IdxExpr
  | add    : IdxExpr → IdxExpr → IdxExpr
  | mul    : Nat → IdxExpr → IdxExpr
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-- Evaluate an index expression under a loop-variable environment.
    Used by tests and by constant-folding of indices; the emitter renders the
    symbolic form instead. -/
def IdxExpr.eval (env : Nat → Nat) : IdxExpr → Nat
  | .const n          => n
  | .var v            => env v
  | .affine base s v  => base + s * env v
  | .add a b          => a.eval env + b.eval env
  | .mul c e          => c * e.eval env

/-- Which buffer a gather lane reads from. `mem` is the unified flat scalar
    memory the emitter realizes as one mutable array (inputs, temporaries, and
    output all live there at distinct offsets). `table name` is a top-level
    compile-time `ConstTable` — the NTT twiddles, addressed by an affine index
    into the precomputed `ω` powers. -/
inductive BufRef where
  | mem   : BufRef
  | table : String → BufRef
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-- Loop-shaped statement IR sitting between the matrix layer and emission.

    Exactly five constructors (umbrella D1). `compute` is the only leaf
    carrying arithmetic; everything else is structural.

    `compute kernel gathers scatter accumulate`:
    - `kernel` is an `ArithExpr` whose `.var j` leaves are *gather lanes*:
      lane `j` reads `gathers[j]!`, a `(buffer, affine-index)` pair.
    - `scatter` addresses the `mem` slot written.
    - `accumulate` selects `mem[scatter] += kernel` (matmul / NTT inner
      product) over `mem[scatter] = kernel` (constant write, copy).

    The design (D1) writes `compute` with a single `gather`/`scatter` pair.
    A single affine gather cannot address matmul's two operands, nor a `mem`
    read plus a twiddle-table read, so the field is a *list* of gather lanes —
    one `(BufRef, IdxExpr)` per kernel `.var`. This keeps the five `LoopExpr`
    / five `IdxExpr` constructor counts the spec fixes while making the inner
    product and the runtime twiddle lookup expressible with affine indices
    only (design D4). -/
inductive LoopExpr where
  | for'    : (idx : Nat) → (lo hi : Nat) → (body : LoopExpr) → LoopExpr
  | seq     : LoopExpr → LoopExpr → LoopExpr
  | compute : (kernel : ArithExpr) → (gathers : List (BufRef × IdxExpr)) →
              (scatter : IdxExpr) → (accumulate : Bool) → LoopExpr
  | temp    : (size : Nat) → (body : LoopExpr) → LoopExpr
  | nop     : LoopExpr
  deriving Repr, BEq, Hashable, Inhabited

/-- Number of IR nodes (structural; the embedded kernel `ArithExpr` counts as
    one regardless of its own size). -/
def LoopExpr.size : LoopExpr → Nat
  | .for' _ _ _ body    => 1 + body.size
  | .seq a b            => 1 + a.size + b.size
  | .compute _ _ _ _    => 1
  | .temp _ body        => 1 + body.size
  | .nop                => 1

/-- Set of loop-variable indices bound by `for'` nodes anywhere in the tree.
    Used by tests to confirm a lowering introduced the loop nest it should. -/
def LoopExpr.usedVars : LoopExpr → List Nat
  | .for' idx _ _ body  => idx :: body.usedVars
  | .seq a b            => a.usedVars ++ b.usedVars
  | .compute _ _ _ _    => []
  | .temp _ body        => body.usedVars
  | .nop                => []

/-- Everything the emitter needs to realize a lowered matrix expression as a
    self-contained Rust function over a flat `mem` array. The lowering
    (`MatrixExpr.lowerLoop`) produces it; `emitLoopProgram` consumes it. -/
structure LoopProgram where
  /-- Positional input count `x0..x(arity-1)`, seeded into `mem[0..arity)`. -/
  arity   : Nat
  /-- Total `mem` slots used (inputs + intermediates + output). -/
  memSize : Nat
  /-- Offset of the result region in `mem`. -/
  outBase : Nat
  /-- Result element count `m·n`, returned as `[u32; outSize]`. -/
  outSize : Nat
  /-- Twiddle tables (forward / inverse NTT) referenced by the body. -/
  tables  : List ConstTable
  /-- The loop nest computing the result into `mem[outBase ..]`. -/
  body    : LoopExpr
  deriving Repr, Inhabited

end TRZK
