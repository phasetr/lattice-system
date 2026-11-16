import Checker.Support
import Checker.TestSupport
import Checker.LakeIsolation

/-! Pinned environment inspection for vocabulary and exact source skeletons.
Checker compilation is distinct from compiling the mathematical production target.
-/
namespace Checker.SemanticDriver
open Lean System Checker.CheckAll

/-- Semantic-driver records are interpreted as exact tab-separated fields. -/
abbrev Row := Array String

/-- One-based fields retain the prior AWK driver conventions. -/
def col (row : Row) (index : Nat) : String := row[index - 1]?.getD ""

/-- Exact physical records, removing only the terminal LF sentinel. -/
def lines (text : String) : Array String :=
  if text.isEmpty then #[] else
    let rows := split text "\n"
    if text.endsWith "\n" then rows.pop else rows

/-- Read a semantic table's data records without Unicode whitespace normalization. -/
def table (root : FilePath) (name : String) : IO (Array Row) := do
  let text ← Checker.RegistryIO.read root name .historical
  let rows := lines text
  return (rows.extract 1 rows.size).map (split · "\t")

/-- Resolve fixture boundaries before accepting an alternate semantic-checker source. -/
def validateRoot (project target : FilePath) (fixture : Bool) (alternate : Bool) : IO (FilePath × FilePath) := do
  let project ← IO.FS.realPath project; let target ← IO.FS.realPath target
  let checker ← if fixture then do
    let some owner ← IO.getEnv "LATTICE_TEST_ROOT" | throw <| IO.userError "fixture mode requires LATTICE_TEST_ROOT"
    let owner ← IO.FS.realPath owner
    require (!pathWithin owner.toString project.toString) "LATTICE_TEST_ROOT must be repository-external"
    require (owner.toString != "/" && !pathWithin project.toString owner.toString)
      "LATTICE_TEST_ROOT must not contain the repository"
    require (pathWithin target.toString owner.toString) "fixture root must be below LATTICE_TEST_ROOT"
    match ← IO.getEnv "LATTICE_SKELETON_CHECKER_DIR" with
    | some root =>
      if !alternate then pure project else do
        let root ← IO.FS.realPath root
        require (pathWithin root.toString owner.toString) "fixture checker must be below LATTICE_TEST_ROOT"
        pure root
    | none => pure project
  else do
    require (trim (← git target #["rev-parse","--show-toplevel"]) == target.toString)
      "ROOT must be repository top; fixture mode is explicit"
    require ((← IO.getEnv "LATTICE_SEMANTIC_CACHE").isNone) "production run cannot substitute semantic artifacts"
    if alternate then
      require ((← IO.getEnv "LATTICE_SKELETON_CHECKER_DIR").isNone) "production run cannot substitute the semantic checker"
    discard <| Checker.RegistryIO.load target (← Checker.RegistryIO.currentProfile project target) #["sources"]
    pure project
  return (target,checker)

/-- Validate a header before any declaration or module inspection. -/
def header (root : FilePath) (name expected : String) : IO Unit := do
  let text ← Checker.RegistryIO.read root name .historical
  require ((lines text)[0]?.getD "" == expected) s!"bad {name}.tsv header"

/-- Inspect data only from the explicit required input collection. -/
def required (root : FilePath) (names : Array String) : IO Unit := do
  let view ← Checker.RegistryIO.load root .historical names
  names.forM fun name => require (view.files.contains (Checker.RegistryIO.tablePath name)) s!"missing registry/{name}.tsv"

/-- One inspection shares its pinned compiler and canonical project import path as immutable inputs. -/
private structure Runtime where
  compiler : FilePath
  basePath : String

/-- Resolve the project Lake environment once, after the entry route's ownership and input guards. -/
private def loadRuntime (project compiler : FilePath) : IO Runtime := do
  return ⟨compiler,trim (← output project "lake" #["env","printenv","LEAN_PATH"])⟩

/-- Run a pinned compiler with an explicit inspection runtime and the same child-only path overrides. -/
private def leanWith (runtime : Runtime) (project temporary source : FilePath) (args : Array String := #[])
    (additional : Array (String × Option String) := #[]) : IO Unit := do
  let defaults := #[("LEAN_PATH",some (temporary.toString ++ ":" ++ runtime.basePath))]
  let environment := defaults.filter (fun pair => !additional.any (fun item => pair.1 == item.1)) ++ additional
  let result ← IO.Process.output {
    cmd := runtime.compiler.toString
    args := #[source.toString] ++ args
    cwd := some project
    env := environment }
  require (result.exitCode == 0) (result.stdout ++ result.stderr)

/-- Retain the standalone helper API; entry routes share a runtime across all of their compiler calls. -/
def lean (project temporary compiler source : FilePath) (args : Array String := #[])
    (additional : Array (String × Option String) := #[]) : IO Unit := do
  leanWith (← loadRuntime project compiler) project temporary source args additional

/-- Bind the checker artifact cache to all source bytes, compiler bytes and the compile recipe. -/
def checkerKey (project checker compiler : FilePath) (kind : String) : IO String := do
  let source ← IO.FS.readFile (checker / "Checker/Semantic.lean")
  let body ← IO.FS.readFile (checker / "Checker" / (kind ++ ".lean"))
  let compilerOid ← git project #["hash-object",compiler.toString]
  return trim (← output project "git" #["hash-object","--stdin"]
    (some (source ++ "\x00" ++ body ++ "\x00" ++ trim compilerOid ++ "\x00semantic-olean-v1:--root;-o")))

/-- Compile one source-bound checker pair, sharing only completed artifacts in an owned suite cache. -/
private def prepareCheckerWith (runtime : Runtime) (project checker temporary : FilePath) (kind : String) : IO FilePath := do
  let compiler := runtime.compiler
  let before ← checkerKey project checker compiler kind
  let destination ← match ← IO.getEnv "LATTICE_SEMANTIC_CACHE" with
    | none => pure (temporary / "semantic")
    | some cache =>
      let some owner ← IO.getEnv "LATTICE_TEST_ROOT" | throw <| IO.userError "semantic cache is fixture-only"
      let owner ← IO.FS.realPath owner; let cache := FilePath.mk cache
      require (owner.toString != "/" && !pathWithin owner.toString project.toString &&
        !pathWithin project.toString owner.toString) "semantic cache needs an external owned test root"
      require (!(cache.toString.splitOn "/").contains "..") "invalid semantic cache path"
      let some parent := cache.parent | throw <| IO.userError "semantic cache has no parent"
      require (pathWithin (← IO.FS.realPath parent).toString owner.toString) "semantic cache escapes owned fixtures"
      if ← cache.pathExists then
        require ((← cache.symlinkMetadata).type == .dir) "semantic cache must be an owned directory"
      else IO.FS.createDir cache
      pure (cache / before)
  let marker := destination / "complete"
  if ← marker.pathExists then
    require ((← destination.symlinkMetadata).type == .dir && (← marker.symlinkMetadata).type == .file)
      "semantic cache entry must contain regular owned artifacts"
    let completed ← parse (← IO.FS.readFile marker)
    require (exactKeys completed #["source","artifacts"] && (← str completed "source") == before)
      "semantic cache completion identity drift"
    let artifacts ← field completed "artifacts"
    require (exactKeys artifacts #["Semantic",kind]) "semantic cache artifact inventory drift"
    for name in #["Semantic",kind] do
      let artifact := destination / "Checker" / (name ++ ".olean")
      require ((← artifact.symlinkMetadata).type == .file)
        "semantic cache artifact is missing or symbolic"
      require ((← str artifacts name) == trim (← git project #["hash-object",artifact.toString]))
        "semantic cache artifact content drift"
    return destination
  require (!(← destination.pathExists)) "incomplete semantic cache entry"
  IO.FS.createDirAll (destination / "Checker")
  leanWith runtime project destination (checker / "Checker/Semantic.lean")
    #["--root=" ++ checker.toString,"-o",(destination / "Checker/Semantic.olean").toString]
  leanWith runtime project destination (checker / "Checker" / (kind ++ ".lean"))
    #["--root=" ++ checker.toString,"-o",(destination / "Checker" / (kind ++ ".olean")).toString]
  require ((← checkerKey project checker compiler kind) == before) "semantic checker source changed during compilation"
  let artifacts ← #["Semantic",kind].mapM fun name => do
    pure (name,toJson (trim (← git project #["hash-object",(destination / "Checker" / (name ++ ".olean")).toString])))
  IO.FS.writeFile marker (Json.mkObj [("source",toJson before),("artifacts",Json.mkObj artifacts.toList)]).compress
  return destination

/-- Preserve the independent checker-preparation API without exposing a runtime substitution option. -/
def prepareChecker (project checker temporary compiler : FilePath) (kind : String) : IO FilePath := do
  prepareCheckerWith (← loadRuntime project compiler) project checker temporary kind

/-- Thread successful compilations through each complete pass, rejecting only a pass with no progress. -/
private partial def compilePending (modules : Array Row)
    (compile : Std.HashSet String → Row → IO (Std.HashSet String)) (compiled : Std.HashSet String) : IO Unit := do
  if compiled.size >= modules.size then return
  let before := compiled.size
  let next ← modules.foldlM compile compiled
  require (next.size > before) "registered module import graph is cyclic or incomplete"
  compilePending modules compile next

/-- Elaborate registered leaves in the exact direct-import dependency order. -/
private def compileModulesWith (runtime : Runtime) (project target temporary semantic : FilePath)
    (modules imports : Array Row) (strict : Bool := true) : IO Unit := do
  let names := modules.map (col · 1)
  let search := temporary.toString ++ ":" ++ semantic.toString
  let compile := fun (compiled : Std.HashSet String) (row : Row) => do
      let name := col row 1; let source := col row 2
      if compiled.contains name then return compiled
      require (row.size == 3 && !name.isEmpty && !source.isEmpty && (strict || !(col row 3).isEmpty)) "malformed module row"
      require ((name.splitOn ".").all fun p => !p.isEmpty &&
        (p.toList.head! == '_' || (('A' ≤ p.toList.head! && p.toList.head! ≤ 'Z') || ('a' ≤ p.toList.head! && p.toList.head! ≤ 'z'))) && p.toList.all (fun c => (('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')) || c == '_')) "unsafe module name"
      require (!source.startsWith "/" && (source.splitOn "..").length == 1 && source.endsWith ".lean") "unsafe source path"
      require (← (target / source).pathExists) s!"missing source path {source}"
      let blocked := imports.any fun r => col r 1 == name && names.contains (col r 3) && !compiled.contains (col r 3)
      if blocked then return compiled
      let destination := temporary / ((name.replace "." "/") ++ ".olean")
      if let some parent := destination.parent then IO.FS.createDirAll parent
      let result ← IO.Process.output {
        cmd := runtime.compiler.toString
        args := (if strict then #["-DwarningAsError=true"] else #[]) ++ #["--root=" ++ target.toString,(target / source).toString,"-o",destination.toString]
        cwd := some project
        env := #[("LEAN_PATH",some (search ++ ":" ++ runtime.basePath))] }
      require (result.exitCode == 0) s!"failed to elaborate registered module {name}\n{result.stdout}{result.stderr}"
      pure (compiled.insert name)
  compilePending modules compile {}

/-- Preserve standalone module compilation while entry routes reuse their already resolved project path. -/
def compileModules (project target temporary compiler semantic : FilePath) (modules imports : Array Row) (strict : Bool := true) : IO Unit := do
  compileModulesWith (← loadRuntime project compiler) project target temporary semantic modules imports strict

/-- Reconstruct exact semantic hashes from the environment dumper's escaped single-line encodings. -/
def declarationRows (project : FilePath) (environment : String) (skeleton : Bool) : IO (Array Row) :=
  (lines environment).foldlM (fun result line => do
    let row := split line "\t"
    if col row 1 == "D" then
      let typeIndex := if skeleton then 18 else 12
      let typeOid := trim (← output project "git" #["hash-object","--stdin"] (some (col row typeIndex)))
      let valueOid := trim (← output project "git" #["hash-object","--stdin"] (some (col row (typeIndex+1))))
      if skeleton then
        pure (result.push (#[col row 2,col row 3,col row 4,typeOid,valueOid] ++ row.extract 4 17))
      else
        pure (result.push (row.extract 1 11 ++ #[typeOid,valueOid]))
    else pure result) #[]

/-- Stable sorting of field rows reproduces the C-locale set comparison. -/
def sorted (rows : Array Row) : Array String :=
  (rows.map fun row => String.intercalate "\t" row.toList).qsort (· < ·)

/-- Read a last-declaration index, keeping the old associative-array interpretation. -/
def indexBy (rows : Array Row) (column : Nat) : Std.HashMap String Row :=
  rows.foldl (fun result row => result.insert (col row column) row) {}

/-- Compare the ordered direct imports observed in the environment to the explicit registry. -/
def importRows (environment : String) : Array Row :=
  let (_,result) := (lines environment).foldl (fun (positions,result) line =>
    let row := split line "\t"
    if col row 1 == "I" && col row 4 != "Init" then
      let owner := col row 2; let position := positions[owner]?.getD 0 + 1
      (positions.insert owner position,result.push (#[owner,toString position] ++ row.extract 3 7))
    else (positions,result)) (({},#[]) : Std.HashMap String Nat × Array Row)
  result

/-- Finite import reachability, without adding assumptions to mathematical vertex types. -/
def reachability (modules imports : Array Row) : Std.HashSet (String × String) :=
  let names := modules.map (col · 1)
  let reach : Std.HashSet (String × String) := names.foldl (fun result name => result.insert (name,name)) {}
  let reach := imports.foldl (fun reach row =>
    if names.contains (col row 1) && names.contains (col row 3) then reach.insert (col row 1,col row 3) else reach) reach
  names.foldl (fun reach k => names.foldl (fun reach i => names.foldl (fun reach j =>
    if reach.contains (i,k) && reach.contains (k,j) then reach.insert (i,j) else reach) reach) reach) reach

/-- Append a failed rule without introducing effects or changing the ordered diagnostic stream. -/
private def record (failures : Array String) (valid : Bool) (message : String) : Array String :=
  if valid then failures else failures.push message

/-- Preserve one historical diagnostic pass: its complete immutable error array fails before the next pass. -/
private def diagnosticPass (label : String) (failures : Array String) : IO Unit := do
  require failures.isEmpty (String.intercalate "\n" failures.toList ++ "; " ++ label)

/-- Enforce vocabulary declaration, generated-parent, finiteness and exact environment contracts. -/
def validateVocabulary (modules imports vocabulary actual : Array Row) (environment : String) : IO Unit := do
  let registered := indexBy vocabulary 2
  let failures := actual.foldl (fun errors row =>
    let name := col row 2
    match registered[name]? with
    | none => errors.push s!"unregistered declaration: {name}"
    | some expected =>
      let errors := record errors (!(#["theorem","axiom","opaque","quotient"].contains (col row 3))) s!"forbidden primary declaration kind: {name}"
      let errors := record errors (col row 5 != "true") s!"Prop-valued vocabulary declaration: {name}"
      let errors := record errors (col row 6 != "true") s!"direct sorryAx dependency: {name}"
      let errors := record errors (col row 7 != "true") s!"transitive sorryAx dependency: {name}"
      let errors := record errors (col expected 9 != "graph_core" || col row 8 == "true") s!"graph_core declaration does not mention SimpleGraph: {name}"
      let errors := record errors (col expected 10 != "none" || col row 9 != "true") s!"global vocabulary declaration requires Fintype: {name}"
      let errors := record errors (col expected 10 != "local_operation" || col row 9 == "true") s!"local_operation declaration lacks Fintype: {name}"
      let errors := record errors (col expected 10 != "explicit_finite_volume" || (col row 9 == "true" || col row 10 == "true"))
        s!"explicit_finite_volume declaration lacks a finite carrier or Finset data: {name}"
      if col row 4 == "NONE" then
        record errors (col expected 5 == "primary" && col expected 6 == "NONE") s!"unsubstantiated generated origin/parent: {name}"
      else
        let parent := registered[col row 4]?.getD #[]
        record errors (!parent.isEmpty && col expected 5 == "generated" && col expected 6 == col parent 1 &&
          col expected 9 == "generated" && col expected 10 == "inherited") s!"generated declaration parent metadata mismatch: {name}") #[]
  require failures.isEmpty (String.intercalate "\n" failures.toList ++ "; semantic declaration policy failed")
  diagnosticPass "registry contains a semantically unverifiable declaration kind" <| vocabulary.foldl
    (fun errors row => record errors (col row 4 != "notation")
      s!"notation has no ConstantInfo and cannot be a vocabulary declaration: {col row 2}") #[]
  let expected := vocabulary.map fun row => #[col row 2,col row 3,col row 4,col row 7,col row 8]
  let observed := actual.map fun row => #[col row 2,col row 1,col row 3,col row 11,col row 12]
  require (sorted expected == sorted observed) "declaration/module/kind/type_oid/declaration_oid registry does not exactly match the environment"
  diagnosticPass "production imports must target registered project modules or Mathlib" <| imports.foldl (fun errors row =>
    let name := col row 3
    record errors (name == "LatticeSystem" || name.startsWith "LatticeSystem." || name == "Mathlib" || name.startsWith "Mathlib.")
      s!"unauthorized production import: {name}") #[]
  require (sorted imports == sorted (importRows environment)) "direct imports are missing, reordered, drifted, or unauthorized"
  let reach := reachability modules imports
  let failures := record #[] (modules.any (col · 3 == "umbrella")) "no umbrella module registered"
  diagnosticPass "registered umbrella reachability failed" <| modules.foldl (fun errors owner =>
    modules.foldl (fun errors target =>
      let errors := if col owner 3 == "umbrella" && col target 3 == "leaf" then
        record errors (reach.contains (col owner 1,col target 1)) s!"umbrella cannot reach leaf: {col owner 1} -> {col target 1}"
        else errors
      if col owner 3 == "root" then
        record errors (reach.contains (col owner 1,col target 1)) s!"root cannot reach registered module: {col owner 1} -> {col target 1}"
      else errors) errors) failures

/-- Parse explicit vocabulary fixture/dump options without executing a command string. -/
def vocabularyOptions : List String → Bool → Bool → Option String → Except String (Bool × Bool × Option String)
  | [], fixture, dump, root => .ok (fixture,dump,root)
  | "--dump" :: rest, fixture, _, root => vocabularyOptions rest fixture true root
  | "--fixture" :: target :: rest, _, dump, _ => vocabularyOptions rest true dump (some target)
  | ["--fixture"], _, _, _ => .error "--fixture requires ROOT"
  | argument :: rest, fixture, dump, root =>
    if argument.startsWith "--" then .error s!"unknown option: {argument}"
    else if root.isSome then .error "multiple roots supplied"
    else vocabularyOptions rest fixture dump (some argument)

/-- Execute semantic vocabulary inspection with source-bound checker artifacts and isolated module outputs. -/
def vocabulary (project : FilePath) (args : List String) : IO Unit := do
  try
    let (fixture,dump,target) ← IO.ofExcept (vocabularyOptions args false false none)
    let (target,checker) ← validateRoot project (target.getD project.toString) fixture false
    required target #["modules","vocabulary","imports"]
    header target "modules" "module\tsource_path\trole"
    header target "vocabulary" "vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope"
    header target "imports" "module\tposition\timported_module\tis_exported\tis_meta\timport_all"
    let modules ← table target "modules"; let imports ← table target "imports"
    IO.FS.withTempDir fun temporary => do
      let compiler := (← toolchainRoot project) / "bin/lean"
      let runtime ← loadRuntime project compiler
      let semantic ← prepareCheckerWith runtime project checker temporary "Vocabulary"
      compileModulesWith runtime project target temporary semantic modules imports false
      IO.FS.writeFile (temporary / "modules.list") (String.join (modules.toList.map fun r => col r 1 ++ "\n"))
      let source := "module\n" ++ String.join (modules.toList.map fun r => "public import " ++ col r 1 ++ "\n") ++
        "public meta import Checker.Vocabulary\n\n#vocabulary_dump " ++ (toJson (temporary / "modules.list").toString).compress ++
        " " ++ (toJson (temporary / "environment.tsv").toString).compress ++ "\n"
      IO.FS.writeFile (temporary / "VocabularyRun.lean") source
      leanWith runtime project temporary (temporary / "VocabularyRun.lean")
        #["--root=" ++ temporary.toString,"-o",(temporary / "VocabularyRun.olean").toString]
        #[("LEAN_PATH",some (temporary.toString ++ ":" ++ semantic.toString ++ ":" ++ runtime.basePath))]
      let environment ← IO.FS.readFile (temporary / "environment.tsv")
      let actual ← declarationRows project environment false
      if dump then
        IO.println "module\tdeclaration\tdeclaration_kind\tparent_declaration\ttype_oid\tdeclaration_oid\tis_prop\tdirect_sorry\ttransitive_sorry\tuses_simple_graph\tuses_fintype\tuses_finset"
        for line in sorted (actual.map fun r => #[col r 1,col r 2,col r 3,col r 4,col r 11,col r 12,col r 5,col r 6,col r 7,col r 8,col r 9,col r 10]) do IO.println line
      else
        validateVocabulary modules imports (← table target "vocabulary") actual environment
        IO.println "check-vocabulary: ok"
  catch error => throw <| IO.userError s!"check-vocabulary: {error}"

/-- A frozen source binds every target exactly once; staged earlier sources may bind a subset. -/
def skeletonCoverage (progress claims bindings : Array Row) : IO Unit := do
  let complete := indexBy progress 1; let known := indexBy claims 1
  let failures := claims.foldl (fun errors claim =>
    if #["skeleton_frozen","proof_active","complete"].contains (col (complete[col claim 2]?.getD #[]) 2) &&
        col claim 12 == "false" && col claim 6 != "out_of_scope" then
      record errors (bindings.any (col · 1 == col claim 1)) s!"skeleton source lacks a binding {col claim 1}"
    else errors) #[]
  let failures := bindings.foldl (fun errors binding =>
    record errors ((bindings.filter (col · 1 == col binding 1)).size == 1)
      s!"duplicate binding {col binding 1}") failures
  diagnosticPass "source skeleton coverage failed" <| progress.foldl (fun errors source =>
    if #["skeleton_frozen","proof_active","complete"].contains (col source 2) then
      let count := bindings.filter fun b => col (known[col b 1]?.getD #[]) 2 == col source 1
      let targets := claims.filter fun c => col c 2 == col source 1 && col c 12 == "false" && col c 6 != "out_of_scope"
      record errors (count.size == targets.size) s!"binding count does not match formalization targets in {col source 1}"
    else errors) failures

/-- Match every expected statement, proof and axiom to exactly the observed module declaration. -/
def skeletonDeclarations (bindings axioms actual : Array Row) : IO Unit := do
  let (expected,failures) := bindings.foldl (fun (expected,errors) row =>
    let entries := #[#[col row 4,col row 2,col row 5,col row 7,col row 8,"statement",col row 1,col row 6]]
    let entries := if col row 3 != "NONE" then entries.push #[col row 4,col row 3,col row 10,col row 11,col row 12,"proof",col row 1,col row 6] else entries
    let entries := if col row 13 != "NONE" then entries.push #[col row 4,col row 13,"theorem",col row 14,"NONE","nonvacuity",col row 1,col row 6] else entries
    entries.foldl (fun (expected,errors) declaration =>
      let key := (col declaration 1,col declaration 2)
      let errors := record errors (!expected.contains key) s!"duplicate registered declaration {key.2}"
      (expected.insert key declaration,errors)) (expected,errors))
    (({},#[]) : Std.HashMap (String × String) Row × Array String)
  let (expected,failures) := axioms.foldl (fun (expected,errors) row =>
    let key := (col row 3,col row 2)
    let errors := record errors (!expected.contains key) s!"duplicate registered declaration {key.2}"
    (expected.insert key #[key.1,key.2,"axiom",col row 8,"NONE","axiom",col row 1,"axiom"],errors)) (expected,failures)
  let (observed,failures) := actual.foldl (fun (observed,errors) row =>
    let key := (col row 1,col row 2)
    let observed := observed.insert key
    match expected[key]? with
    | none => (observed,errors.push s!"extra declaration {key.2}")
    | some expectedRow =>
      let errors := record errors (col expectedRow 3 == col row 3) s!"wrong declaration kind {key.2} expected={col expectedRow 3} actual={col row 3}"
      let errors := record errors (col expectedRow 4 == "PENDING" || col expectedRow 4 == col row 4) s!"wrong type OID {key.2}"
      (observed,record errors (#["NONE","PENDING"].contains (col expectedRow 5) || col expectedRow 5 == col row 5) s!"wrong value OID {key.2}"))
    (({},failures) : Std.HashSet (String × String) × Array String)
  diagnosticPass "declaration registry/environment mismatch" <| expected.fold
    (fun errors key _ => record errors (observed.contains key) s!"missing or wrong-module declaration {key.1}\x1c{key.2}") failures

/-- Preserve exact primary propositions, proof types, nonvacuity and direct-hole ownership. -/
def skeletonShapes (bindings actual : Array Row) : IO Unit := do
  let statements := indexBy bindings 2; let proofs := indexBy (bindings.filter (col · 3 != "NONE")) 3
  let nonvacuity := indexBy (bindings.filter (col · 13 != "NONE")) 13
  diagnosticPass "primary/proof-hole bijection failed" <| actual.foldl (fun errors row =>
    let name := col row 2; let direct := (col row 7).toNat?.getD 0; let transitive := col row 8 == "true"
    if let some binding := statements[name]? then
      let errors := record errors (direct == 0 && !transitive) s!"primary statement depends on sorryAx {name}"
      let errors := record errors (col row 14 != "true") s!"literal True primary statement {name}"
      record errors (col binding 6 != "proof_proposition" || col row 15 == "true") s!"proof proposition is not Prop-valued {name}"
    else if let some binding := proofs[name]? then
      let errors := record errors (col row 6 == "true") s!"proof declaration is not Prop-valued {name}"
      let errors := record errors (col row 18 == col binding 2) s!"proof type is not exactly the bound primary statement {name} expected={col binding 2} actual={col row 18}"
      if col binding 12 == "NONE" then
        record errors (direct == 1 && transitive) (if direct == 0 && transitive then
          s!"hidden or transitive-only sorryAx {name}" else
          s!"proof stub needs exactly one direct sorryAx {name}")
      else record errors (direct == 0 && !transitive) s!"completed proof depends on sorryAx {name}"
    else if let some binding := nonvacuity[name]? then
      let errors := record errors (direct == 0 && !transitive) s!"nonvacuity declaration depends on sorryAx {name}"
      let errors := record errors (col row 16 != "true") s!"nonvacuity declaration concludes True {name}"
      let errors := record errors (col row 17 != "true") s!"nonvacuity declaration follows from its own hypotheses {name}"
      record errors ((col row 9).splitOn "," |>.contains (col binding 2)) s!"nonvacuity declaration does not reference its bound statement {name}"
    else record errors (direct == 0 && !transitive) s!"unregistered sorryAx declaration {name}") #[]

/-- Actual setup uses must be earlier and admitted, with assumption context occurring in binders. -/
def skeletonContext (claims bindings vocabulary contexts dependencies modules actual : Array Row) : IO Unit := do
  let sequence : Std.HashMap String Nat := (claims.zipIdx).foldl (fun result (row,i) => result.insert (col row 1) (i+1)) {}
  let claimOf := indexBy bindings 2
  let registered : Std.HashSet String := (bindings ++ vocabulary).foldl (fun result row => result.insert (col row 2)) {}
  let rootOf := fun name : String => (name.splitOn ".").head!
  let projects : Std.HashSet String := modules.foldl (fun result row => result.insert (rootOf (col row 1))) {}
  let (admitted,context,assumptions) := contexts.foldl (fun (admitted,context,assumptions) row =>
    let edge := (col row 1,col row 3)
    (admitted.insert edge,context.insert edge,if col row 4 == "assumption" then assumptions.insert edge else assumptions))
    (({},{},{}) : Std.HashSet (String × String) × Std.HashSet (String × String) × Std.HashSet (String × String))
  let (admitted,forward) := dependencies.foldl (fun (admitted,forward) row =>
    let edge := if col row 2 == "required_by" then (col row 3,col row 1) else (col row 1,col row 3)
    (admitted.insert edge,if col row 2 == "required_by" then forward.insert edge else forward))
    (admitted,({} : Std.HashSet (String × String)))
  let (used,guards,failures) := actual.foldl (fun (used,guards,errors) row =>
    if let some owner := claimOf[col row 2]? then
      let claim := col owner 1
      let (used,errors) := ((col row 9 ++ "," ++ col row 10).splitOn ",").foldl (fun (used,errors) name =>
        if name.isEmpty then (used,errors) else
        let used := if let some setup := claimOf[name]? then
          if col setup 1 != claim then used.insert (claim,col setup 1) else used
          else used
        (used,record errors (!projects.contains (rootOf name) || name == col row 2 || registered.contains name)
          s!"primary statement uses an unregistered project constant {name}")) (used,errors)
      let guards := ((col row 12 ++ "," ++ col row 13).splitOn ",").foldl (fun guards name =>
        if let some setup := claimOf[name]? then guards.insert (claim,col setup 1) else guards) guards
      (used,guards,errors)
    else (used,guards,errors))
    (({},{},#[]) : Std.HashSet (String × String) × Std.HashSet (String × String) × Array String)
  let failures := context.fold (fun errors edge =>
    let errors := record errors (used.contains edge) s!"registered context is absent from statement {edge.1}\x1c{edge.2}"
    record errors (!assumptions.contains edge || guards.contains edge) s!"assumption context is not a binder or antecedent {edge.1}\x1c{edge.2}") failures
  diagnosticPass "claim-context semantic mismatch" <| used.fold (fun errors edge =>
    if !admitted.contains edge then
      record errors false s!"actual setup reference lacks claim-context or dependency {edge.1}\x1c{edge.2}"
    else if forward.contains edge then
      record errors (sequence[edge.2]?.getD 0 > sequence[edge.1]?.getD 0) s!"required_by reference does not pull a later claim forward {edge.1}\x1c{edge.2}"
    else record errors (sequence[edge.2]?.getD 0 < sequence[edge.1]?.getD 0) s!"statement references a claim that is not earlier {edge.1}\x1c{edge.2}") failures

/-- Vocabulary use is checked per primary claim, independently of the global declaration registry. -/
def skeletonVocabulary (vocabulary bindings admissions reviews actual : Array Row) : IO Unit := do
  let vocabularyByName := indexBy vocabulary 2; let owners := indexBy bindings 2; let basis := indexBy reviews 1
  diagnosticPass "claim vocabulary admission mismatch" <| actual.foldl (fun errors row =>
    if let some binding := owners[col row 2]? then
      let owner := col binding 1
      ((col row 9 ++ "," ++ col row 10).splitOn ",").foldl (fun errors name =>
        if let some declaration := vocabularyByName[name]? then
          if col (basis[owner]?.getD #[]) 2 != "project_vocabulary" then
            record errors false s!"primary project vocabulary contradicts claim review basis {owner} {col declaration 1}"
          else
            record errors (admissions.any fun a => col a 1 == owner && col a 2 == col declaration 1)
              s!"primary vocabulary use lacks claim-vocabulary admission {owner} {col declaration 1}"
        else errors) errors
    else errors) #[]

/-- Actual nonstandard kernel dependencies exactly match approved claim-to-axiom relations. -/
def skeletonAxioms (bindings axioms approved actual : Array Row) : IO Unit := do
  let owners := bindings.foldl (fun owners row =>
    let owners := owners.insert (col row 2) (col row 1)
    let owners := if col row 3 != "NONE" then owners.insert (col row 3) (col row 1) else owners
    if col row 13 != "NONE" then owners.insert (col row 13) (col row 1) else owners) ({} : Std.HashMap String String)
  let axiomByName := indexBy axioms 2
  let (uses,used,failures) := actual.foldl (fun state row =>
    if let some owner := owners[col row 2]? then
      ((col row 11).splitOn ",").foldl (fun (uses,used,errors) name =>
        if let some registeredAxiom := axiomByName[name]? then
          (uses.insert (owner,col registeredAxiom 1),used.insert (col registeredAxiom 1),errors)
        else
          (uses,used,record errors (#["","propext","Classical.choice","Quot.sound","sorryAx"].contains name)
            s!"unregistered nonstandard axiom {name} used by {col row 2}")) state
    else state) (({},{},#[]) : Std.HashSet (String × String) × Std.HashSet String × Array String)
  let failures := approved.foldl (fun errors edge =>
    record errors (uses.contains (col edge 1,col edge 2)) "approved claim axiom is not used") failures
  let failures := uses.fold (fun errors edge =>
    record errors (approved.any fun r => (col r 1,col r 2) == edge) "unapproved claim axiom is used") failures
  diagnosticPass "claim axiom contract failed" <| axioms.foldl (fun errors registeredAxiom =>
    record errors (used.contains (col registeredAxiom 1)) s!"registered axiom is unused {col registeredAxiom 1}") failures

/-- Reachability isolates unresolved statements from the default mathematical root. -/
def skeletonIsolation (vocabulary statements imports : Array Row) : IO Unit := do
  let reach := reachability (vocabulary ++ statements) imports
  let umbrellas := statements.filter (col · 3 != "leaf")
  let failures := record #[] (umbrellas.size == 1) "skeleton needs exactly one umbrella"
  let root := (vocabulary.filter (col · 3 == "root")).back?.map (col · 1) |>.getD ""
  diagnosticPass "skeleton import isolation failed" <| statements.foldl (fun errors row =>
    let errors := if col row 3 == "leaf" then record errors (reach.contains (((umbrellas.back?).map (col · 1)).getD "",col row 1))
      s!"umbrella misses {col row 1}" else errors
    record errors (root.isEmpty || !reach.contains (root,col row 1)) s!"production root reaches {col row 1}") failures

/-- Only one declaration-local warning exception belongs to each registered unresolved proof. -/
def skeletonWarnings (bindings : Array Row) (environment : String) : IO Unit := do
  let expected : Std.HashSet (String × String) := bindings.foldl (fun result row =>
    if col row 9 == "proof_stub" && col row 12 == "NONE" then result.insert (col row 4,col row 3) else result) {}
  let (seen,failures) := (lines environment).foldl (fun (seen,errors) line =>
      let row := split line "\t"
      if col row 1 == "W" then
        let key := (col row 2,col row 3)
        if col row 4 != "declaration" || key.2 == "NONE" then
          (seen,record errors false s!"unscoped warningAsError suppression in {key.1}")
        else if !expected.contains key then
          (seen,record errors false s!"warningAsError exception is not a registered unresolved proof {key.2}")
        else (seen.insert key (seen[key]?.getD 0 + 1),errors)
      else (seen,errors)) (({},#[]) : Std.HashMap (String × String) Nat × Array String)
  diagnosticPass "warning exception ownership failed" <| expected.fold (fun errors key =>
    record errors (seen[key]?.getD 0 == 1) s!"unresolved proof needs exactly one declaration-local warningAsError exception {key.1}\x1c{key.2}") failures
  diagnosticPass "diagnostic suppression policy failed" <| (lines environment).foldl (fun errors line =>
    let row := split line "\t"
    record errors (col row 1 != "S") s!"forbidden diagnostic suppression {col row 3} in {col row 2}") #[]

/-- Inspect a staged or frozen typed skeleton without treating a contract-only state as source acceptance. -/
def skeleton (project : FilePath) (args : List String) : IO Unit := do
  try
    let (fixture,target) ← match args with
      | [] => pure (false,project)
      | [target] => pure (false,FilePath.mk target)
      | ["--fixture",target] => pure (true,FilePath.mk target)
      | _ => throw <| IO.userError "usage: skeleton [--fixture] ROOT"
    let (target,checker) ← validateRoot project target fixture true
    required target #["phase","sources","source-progress","claims","item-claims","bindings","dependencies",
      "claim-context","axioms","claim-axioms","vocabulary","claim-vocabulary","claim-vocabulary-review",
      "modules","imports","statement-modules","statement-imports"]
    header target "bindings" "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref"
    header target "axioms" "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid"
    let phaseText ← IO.FS.readFile (target / "registry/phase.tsv")
    let phaseLines := lines phaseText
    require (phaseLines.size == 2 && (split phaseText "\n").size ≥ 3) "phase.tsv must have exactly one data row"
    let phase := phaseLines[1]!
    let statements ← table target "statement-modules"; let bindings ← table target "bindings"
    if statements.isEmpty && bindings.isEmpty then
      require (!(#["skeleton","proof"].contains phase)) s!"{phase} capability requires a registered skeleton"
      IO.println "check-skeleton: ok (contract only; no production skeleton)"
      return
    require (!statements.isEmpty && !bindings.isEmpty) "statement modules and bindings must be introduced together"
    skeletonCoverage (← table target "source-progress") (← table target "claims") bindings
    IO.FS.withTempDir fun temporary => do
      let compiler := (← toolchainRoot project) / "bin/lean"
      let runtime ← loadRuntime project compiler
      let semantic ← prepareCheckerWith runtime project checker temporary "Skeleton"
      let vocabulary ← table target "modules"; let modules := vocabulary ++ statements
      let vocabularyImports ← table target "imports"; let statementImports ← table target "statement-imports"
      compileModulesWith runtime project target temporary semantic modules (vocabularyImports ++ statementImports)
      for (file,rows) in #[("modules.list",modules),("statement-modules.list",statements)] do
        IO.FS.writeFile (temporary / file) (String.join (rows.toList.map fun r => col r 1 ++ "\n"))
      let imports := String.join (modules.toList.map fun row => "import " ++ col row 1 ++ "\n")
      let quoted := fun path : FilePath => (toJson path.toString).compress
      IO.FS.writeFile (temporary / "SkeletonRun.lean") (imports ++ "import Checker.Skeleton\n\n#skeleton_dump " ++
        quoted (temporary / "statement-modules.list") ++ " " ++ quoted (temporary / "environment.tsv") ++
        " " ++ quoted target ++ " " ++ quoted (target / "registry/statement-modules.tsv") ++ "\n")
      let search := temporary.toString ++ ":" ++ semantic.toString ++ ":" ++ runtime.basePath
      leanWith runtime project temporary (temporary / "SkeletonRun.lean")
        #["--root=" ++ temporary.toString,"-o",(temporary / "SkeletonRun.olean").toString]
        #[("LEAN_PATH",some search)]
      let environment ← IO.FS.readFile (temporary / "environment.tsv")
      let actual ← declarationRows project environment true
      if let some exportPath ← IO.getEnv "LATTICE_SKELETON_ACTUAL_OUT" then
        IO.FS.writeFile exportPath (String.join (actual.toList.map fun r => String.intercalate "\t" r.toList ++ "\n"))
      let axioms ← table target "axioms"
      skeletonDeclarations bindings axioms actual
      skeletonShapes bindings actual
      skeletonContext (← table target "claims") bindings (← table target "vocabulary")
        (← table target "claim-context") (← table target "dependencies") modules actual
      skeletonVocabulary (← table target "vocabulary") bindings (← table target "claim-vocabulary")
        (← table target "claim-vocabulary-review") actual
      skeletonAxioms bindings axioms (← table target "claim-axioms") actual
      require (sorted statementImports == sorted (importRows environment)) "statement import registry/environment mismatch"
      skeletonIsolation vocabulary statements (vocabularyImports ++ statementImports)
      skeletonWarnings bindings environment
      unless fixture do
        require (statements.any fun row => col row 3 == "umbrella" && col row 1 == "LatticeSystem.Skeleton")
          "production skeleton umbrella must be LatticeSystem.Skeleton"
        IO.println "check-skeleton: prepare canonical Lake isolation checker for production inspection"
        let isolationSource := project / "Checker/LakeIsolation.lean"
        let isolationBefore := trim (← git project #["hash-object",isolationSource.toString])
        leanWith runtime project temporary isolationSource
          #["-DwarningAsError=true","--root=" ++ project.toString,"-o",(semantic / "Checker/LakeIsolation.olean").toString]
          #[("LEAN_PATH",some search)]
        require (trim (← git project #["hash-object",isolationSource.toString]) == isolationBefore)
          "Lake isolation checker source changed during compilation"
        IO.FS.writeFile (temporary / "LakeIsolationRun.lean") (imports ++
          "import Checker.LakeIsolation\n#eval Checker.LakeIsolation.check " ++ quoted target ++ "\n")
        leanWith runtime project temporary (temporary / "LakeIsolationRun.lean") #[] #[("LEAN_PATH",some search)]
        runGate target ⟨"lake",#["build","+LatticeSystem.Skeleton"]⟩
      IO.println "check-skeleton: ok"
  catch error => throw <| IO.userError s!"check-skeleton: {error}"

end Checker.SemanticDriver
