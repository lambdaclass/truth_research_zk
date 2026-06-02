/-
  trzk — Compile arithmetic or matrix specs to Rust via optisat saturation.

  Usage:
    .lake/build/bin/trzk <spec.lean> [--matrix] [--output <file>] [--name <funcname>]

  Without --matrix, the spec defines `def spec : ArithExpr := ...`.
  With --matrix, the spec defines `def spec : MatrixExpr := ...` and
  `def out : Nat × Nat := ...` selecting one output cell; the matrix is
  saturated, extracted, then lowered to ArithExpr for that cell and emitted.
-/

structure CompileConfig where
  specFile : Option String := none
  output   : Option String := none
  funcName : String := "arith_spec"
  matrix   : Bool := false
  help     : Bool := false

partial def parseArgs : List String → CompileConfig → CompileConfig
  | [], cfg => cfg
  | "--output" :: v :: rest, cfg => parseArgs rest { cfg with output := some v }
  | "--name"   :: v :: rest, cfg => parseArgs rest { cfg with funcName := v }
  | "--matrix" :: rest, cfg => parseArgs rest { cfg with matrix := true }
  | "--help"   :: rest, cfg => parseArgs rest { cfg with help := true }
  | v :: rest, cfg =>
    if cfg.specFile.isNone && !v.startsWith "--"
    then parseArgs rest { cfg with specFile := some v }
    else parseArgs rest cfg

def showHelp : IO Unit := do
  IO.println "trzk — Compile arithmetic or matrix specs to Rust"
  IO.println ""
  IO.println "Usage: .lake/build/bin/trzk <spec.lean> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --output <file>    Output file path (default: <spec>.rs)"
  IO.println "  --name <funcname>  Function name in generated code (default: arith_spec)"
  IO.println "  --matrix           Interpret spec as MatrixExpr + out : Nat × Nat"
  IO.println "  --help             Show this help"
  IO.println ""
  IO.println "Scalar spec file must define:  def spec : ArithExpr := ..."
  IO.println "Matrix spec file must define:  def spec : MatrixExpr := ..."
  IO.println "                                def out  : Nat × Nat := ..."

/-- Remove `import` lines from user code; the runner provides its own imports. -/
def stripImports (source : String) : String :=
  let lines := source.splitOn "\n"
  let filtered := lines.filter fun line =>
    !(line.trimLeft.startsWith "import ")
  String.intercalate "\n" filtered

/-- Build the runner source for a scalar spec. -/
def buildScalarRunner (userCode funcName outputPath artifactsDir baseName : String) :
    String :=
  s!"import TRZK

open TRZK

{userCode}

def main : IO Unit := do
  IO.FS.createDirAll \"{artifactsDir}\"
  IO.FS.writeFile \"{artifactsDir}/{baseName}.pre.txt\" (toString (repr spec))
  let arity := spec.inputArity
  match optimize RuleSet.babybearNaive spec with
  | none =>
    IO.eprintln \"optimize returned none\"
    IO.Process.exit 1
  | some post =>
    IO.FS.writeFile \"{artifactsDir}/{baseName}.post.txt\" (toString (repr post))
    let code := emitFunction \"{funcName}\" arity post
    IO.FS.writeFile \"{outputPath}\" code
"

/-- Build the runner source for a matrix spec: saturate the matrix, then lower
    every output cell to ArithExpr, run scalar saturation on each, and emit a
    single function returning all cells as `[u32; N]`. -/
def buildMatrixRunner (userCode funcName outputPath artifactsDir baseName : String) :
    String :=
  s!"import TRZK

open TRZK

{userCode}

def main : IO Unit := do
  IO.FS.createDirAll \"{artifactsDir}\"
  IO.FS.writeFile \"{artifactsDir}/{baseName}.pre.txt\" (toString (repr spec))
  match MatrixPipeline.optimize MatrixRuleSet.default spec with
  | none =>
    IO.eprintln \"matrix optimize returned none\"
    IO.Process.exit 1
  | some mpost =>
    IO.FS.writeFile \"{artifactsDir}/{baseName}.mpost.txt\" (toString (repr mpost))
    match mpost.materialize with
    | none =>
      IO.eprintln \"materialize returned none\"
      IO.Process.exit 1
    | some (grid, arity) =>
      let pairs : List (Nat × Nat) :=
        (List.range grid.size).flatMap fun r =>
          (List.range (if grid.size > 0 then grid[0]!.size else 0)).map fun c => (r, c)
      let mut cells : List ArithExpr := []
      for (r, c) in pairs do
        match mpost.lower r c with
        | none =>
          IO.eprintln s!\"lower returned none for cell (\{r}, \{c})\"
          IO.Process.exit 1
        | some (scalar, _) =>
          match optimize RuleSet.babybearNaive scalar with
          | none =>
            IO.eprintln s!\"scalar optimize returned none for cell (\{r}, \{c})\"
            IO.Process.exit 1
          | some post =>
            cells := cells ++ [post]
      let code := emitMatrixFunction \"{funcName}\" arity cells
      IO.FS.writeFile \"{outputPath}\" code
"

def dirOf (path : String) : String :=
  match path.splitOn "/" |>.dropLast with
  | [] => "."
  | parts => String.intercalate "/" parts

def stemOf (path : String) : String :=
  let filename := match path.splitOn "/" with
    | [] => path
    | parts => parts.getLast!
  if filename.endsWith ".rs" then filename.dropRight 3
  else if filename.endsWith ".lean" then filename.dropRight 5
  else filename

def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args {}

  if cfg.help then
    showHelp
    return 0

  let specFile ← match cfg.specFile with
    | some f => pure f
    | none =>
      IO.eprintln "Error: no spec file provided."
      IO.eprintln "Run with --help for usage."
      return 1

  let outputPath := match cfg.output with
    | some p => p
    | none =>
      let base := if specFile.endsWith ".lean" then specFile.dropRight 5 else specFile
      base ++ ".rs"

  let outputDir := dirOf outputPath
  let artifactsDir := s!"{outputDir}/artifacts"
  let baseName := stemOf outputPath

  unless (← System.FilePath.pathExists ⟨specFile⟩) do
    IO.eprintln s!"Error: file '{specFile}' not found."
    return 1
  let userCode ← IO.FS.readFile ⟨specFile⟩
  let cleanCode := stripImports userCode
  let runner :=
    if cfg.matrix then
      buildMatrixRunner cleanCode cfg.funcName outputPath artifactsDir baseName
    else
      buildScalarRunner cleanCode cfg.funcName outputPath artifactsDir baseName

  let tmpPath := "/tmp/trzk_runner.lean"
  IO.FS.writeFile ⟨tmpPath⟩ runner

  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", tmpPath]
  }

  try IO.FS.removeFile ⟨tmpPath⟩ catch _ => pure ()

  if result.exitCode != 0 then
    IO.eprintln "Compilation failed:"
    IO.eprintln s!"--- stderr ---\n{result.stderr}"
    IO.eprintln s!"--- stdout ---\n{result.stdout}"
    return 1

  IO.println s!"Generated: {outputPath}"
  IO.println s!"Artifacts: {artifactsDir}/"
  return 0
