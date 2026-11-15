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
  let text ← IO.FS.readFile (root / "registry" / (name ++ ".tsv"))
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
    pure project
  return (target,checker)

/-- Validate a header before any declaration or module inspection. -/
def header (root : FilePath) (name expected : String) : IO Unit := do
  let text ← IO.FS.readFile (root / "registry" / (name ++ ".tsv"))
  require ((lines text)[0]?.getD "" == expected) s!"bad {name}.tsv header"

/-- Inspect data only from the explicit required input collection. -/
def required (root : FilePath) (names : Array String) : IO Unit :=
  names.forM fun name => do require (← (root / "registry" / (name ++ ".tsv")).pathExists) s!"missing registry/{name}.tsv"

/-- Run a pinned Lean compiler with the inspection-specific output search path. -/
def lean (project temporary compiler source : FilePath) (args : Array String := #[])
    (additional : Array (String × Option String) := #[]) : IO Unit := do
  let base := trim (← output project "lake" #["env","printenv","LEAN_PATH"])
  let defaults := #[("LEAN_PATH",some (temporary.toString ++ ":" ++ base))]
  let environment := defaults.filter (fun pair => !additional.any (fun item => pair.1 == item.1)) ++ additional
  let result ← IO.Process.output {
    cmd := compiler.toString
    args := #[source.toString] ++ args
    cwd := some project
    env := environment }
  require (result.exitCode == 0) (result.stdout ++ result.stderr)

/-- Bind the checker artifact cache to all source bytes, compiler bytes and the compile recipe. -/
def checkerKey (project checker compiler : FilePath) (kind : String) : IO String := do
  let source ← IO.FS.readFile (checker / "Checker/Semantic.lean")
  let body ← IO.FS.readFile (checker / "Checker" / (kind ++ ".lean"))
  let compilerOid ← git project #["hash-object",compiler.toString]
  return trim (← output project "git" #["hash-object","--stdin"]
    (some (source ++ "\x00" ++ body ++ "\x00" ++ trim compilerOid ++ "\x00semantic-olean-v1:--root;-o")))

/-- Compile one source-bound checker pair, sharing only completed artifacts in an owned suite cache. -/
def prepareChecker (project checker temporary compiler : FilePath) (kind : String) : IO FilePath := do
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
  lean project destination compiler (checker / "Checker/Semantic.lean")
    #["--root=" ++ checker.toString,"-o",(destination / "Checker/Semantic.olean").toString]
  lean project destination compiler (checker / "Checker" / (kind ++ ".lean"))
    #["--root=" ++ checker.toString,"-o",(destination / "Checker" / (kind ++ ".olean")).toString]
  require ((← checkerKey project checker compiler kind) == before) "semantic checker source changed during compilation"
  let artifacts ← #["Semantic",kind].mapM fun name => do
    pure (name,toJson (trim (← git project #["hash-object",(destination / "Checker" / (name ++ ".olean")).toString])))
  IO.FS.writeFile marker (Json.mkObj [("source",toJson before),("artifacts",Json.mkObj artifacts.toList)]).compress
  return destination

/-- Elaborate registered leaves in the exact direct-import dependency order. -/
def compileModules (project target temporary compiler semantic : FilePath) (modules imports : Array Row) (strict : Bool := true) : IO Unit := do
  let names := modules.map (col · 1)
  let mut compiled : Std.HashSet String := {}
  let search := temporary.toString ++ ":" ++ semantic.toString
  while compiled.size < modules.size do
    let mut progressed := false
    for row in modules do
      let name := col row 1; let source := col row 2
      if compiled.contains name then continue
      require (row.size == 3 && !name.isEmpty && !source.isEmpty && (strict || !(col row 3).isEmpty)) "malformed module row"
      require ((name.splitOn ".").all fun p => !p.isEmpty &&
        (p.toList.head! == '_' || (('A' ≤ p.toList.head! && p.toList.head! ≤ 'Z') || ('a' ≤ p.toList.head! && p.toList.head! ≤ 'z'))) && p.toList.all (fun c => (('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')) || c == '_')) "unsafe module name"
      require (!source.startsWith "/" && (source.splitOn "..").length == 1 && source.endsWith ".lean") "unsafe source path"
      require (← (target / source).pathExists) s!"missing source path {source}"
      let blocked := imports.any fun r => col r 1 == name && names.contains (col r 3) && !compiled.contains (col r 3)
      if blocked then continue
      let destination := temporary / ((name.replace "." "/") ++ ".olean")
      if let some parent := destination.parent then IO.FS.createDirAll parent
      let base := trim (← output project "lake" #["env","printenv","LEAN_PATH"])
      let result ← IO.Process.output {
        cmd := compiler.toString
        args := (if strict then #["-DwarningAsError=true"] else #[]) ++ #["--root=" ++ target.toString,(target / source).toString,"-o",destination.toString]
        cwd := some project
        env := #[("LEAN_PATH",some (search ++ ":" ++ base))] }
      require (result.exitCode == 0) s!"failed to elaborate registered module {name}\n{result.stdout}{result.stderr}"
      compiled := compiled.insert name; progressed := true
    require progressed "registered module import graph is cyclic or incomplete"

/-- Reconstruct exact semantic hashes from the environment dumper's escaped single-line encodings. -/
def declarationRows (project : FilePath) (environment : String) (skeleton : Bool) : IO (Array Row) := do
  let mut result := #[]
  for line in lines environment do
    let row := split line "\t"
    if col row 1 == "D" then
      let typeIndex := if skeleton then 18 else 12
      let typeOid := trim (← output project "git" #["hash-object","--stdin"] (some (col row typeIndex)))
      let valueOid := trim (← output project "git" #["hash-object","--stdin"] (some (col row (typeIndex+1))))
      if skeleton then
        result := result.push (#[col row 2,col row 3,col row 4,typeOid,valueOid] ++ row.extract 4 17)
      else
        result := result.push (row.extract 1 11 ++ #[typeOid,valueOid])
  return result

/-- Stable sorting of field rows reproduces the C-locale set comparison. -/
def sorted (rows : Array Row) : Array String :=
  (rows.map fun row => String.intercalate "\t" row.toList).qsort (· < ·)

/-- Read a last-declaration index, keeping the old associative-array interpretation. -/
def indexBy (rows : Array Row) (column : Nat) : Std.HashMap String Row :=
  rows.foldl (fun result row => result.insert (col row column) row) {}

/-- Compare the ordered direct imports observed in the environment to the explicit registry. -/
def importRows (environment : String) : Array Row := Id.run do
  let mut positions : Std.HashMap String Nat := {}; let mut result := #[]
  for line in lines environment do
    let row := split line "\t"
    if col row 1 == "I" && col row 4 != "Init" then
      let owner := col row 2; let position := positions[owner]?.getD 0 + 1
      result := result.push (#[owner,toString position] ++ row.extract 3 7)
      positions := positions.insert owner position
  return result

/-- Finite import reachability, without adding assumptions to mathematical vertex types. -/
def reachability (modules imports : Array Row) : Std.HashSet (String × String) := Id.run do
  let names := modules.map (col · 1)
  let mut reach : Std.HashSet (String × String) := names.foldl (fun result name => result.insert (name,name)) {}
  for row in imports do
    if names.contains (col row 1) && names.contains (col row 3) then reach := reach.insert (col row 1,col row 3)
  for k in names do
    for i in names do
      for j in names do
        if reach.contains (i,k) && reach.contains (k,j) then reach := reach.insert (i,j)
  return reach

/-- Preserve one historical diagnostic pass: collect all its errors, then fail before the next pass. -/
def diagnosticPass (label : String) (action : (Bool → String → IO Unit) → IO Unit) : IO Unit := do
  let errors ← IO.mkRef (#[] : Array String)
  action fun valid message => unless valid do errors.modify (·.push message)
  let failures ← errors.get
  require failures.isEmpty (String.intercalate "\n" failures.toList ++ "; " ++ label)

/-- Enforce vocabulary declaration, generated-parent, finiteness and exact environment contracts. -/
def validateVocabulary (modules imports vocabulary actual : Array Row) (environment : String) : IO Unit := do
  let registered := indexBy vocabulary 2
  let errors ← IO.mkRef (#[] : Array String)
  let record := fun (valid : Bool) (message : String) => do
    unless valid do errors.modify (·.push message)
  for row in actual do
    let name := col row 2
    let some expected := registered[name]? | do
      errors.modify (·.push s!"unregistered declaration: {name}")
      continue
    record (!(#["theorem","axiom","opaque","quotient"].contains (col row 3))) s!"forbidden primary declaration kind: {name}"
    record (col row 5 != "true") s!"Prop-valued vocabulary declaration: {name}"
    record (col row 6 != "true") s!"direct sorryAx dependency: {name}"
    record (col row 7 != "true") s!"transitive sorryAx dependency: {name}"
    record (col expected 9 != "graph_core" || col row 8 == "true") s!"graph_core declaration does not mention SimpleGraph: {name}"
    record (col expected 10 != "none" || col row 9 != "true") s!"global vocabulary declaration requires Fintype: {name}"
    record (col expected 10 != "local_operation" || col row 9 == "true") s!"local_operation declaration lacks Fintype: {name}"
    record (col expected 10 != "explicit_finite_volume" || (col row 9 != "true" && col row 10 == "true"))
      s!"explicit_finite_volume declaration is not explicit Finset data: {name}"
    if col row 4 == "NONE" then
      record (col expected 5 == "primary" && col expected 6 == "NONE") s!"unsubstantiated generated origin/parent: {name}"
    else
      let parent := registered[col row 4]?.getD #[]
      record (!parent.isEmpty && col expected 5 == "generated" && col expected 6 == col parent 1 &&
        col expected 9 == "generated" && col expected 10 == "inherited") s!"generated declaration parent metadata mismatch: {name}"
  let failures ← errors.get
  require failures.isEmpty (String.intercalate "\n" failures.toList ++ "; semantic declaration policy failed")
  diagnosticPass "registry contains a semantically unverifiable declaration kind" fun record => do
    for row in vocabulary do
      record (col row 4 != "notation") s!"notation has no ConstantInfo and cannot be a vocabulary declaration: {col row 2}"
  let expected := vocabulary.map fun row => #[col row 2,col row 3,col row 4,col row 7,col row 8]
  let observed := actual.map fun row => #[col row 2,col row 1,col row 3,col row 11,col row 12]
  require (sorted expected == sorted observed) "declaration/module/kind/type_oid/declaration_oid registry does not exactly match the environment"
  diagnosticPass "production imports must target registered project modules or Mathlib" fun record => do
    for row in imports do
      let name := col row 3
      record (name == "LatticeSystem" || name.startsWith "LatticeSystem." || name == "Mathlib" || name.startsWith "Mathlib.")
        s!"unauthorized production import: {name}"
  require (sorted imports == sorted (importRows environment)) "direct imports are missing, reordered, drifted, or unauthorized"
  diagnosticPass "registered umbrella reachability failed" fun record => do
    let reach := reachability modules imports
    record (modules.any (col · 3 == "umbrella")) "no umbrella module registered"
    for owner in modules do
      for target in modules do
        if col owner 3 == "umbrella" && col target 3 == "leaf" then
          record (reach.contains (col owner 1,col target 1)) s!"umbrella cannot reach leaf: {col owner 1} -> {col target 1}"
        if col owner 3 == "root" then
          record (reach.contains (col owner 1,col target 1)) s!"root cannot reach registered module: {col owner 1} -> {col target 1}"

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
      let semantic ← prepareChecker project checker temporary compiler "Vocabulary"
      compileModules project target temporary compiler semantic modules imports false
      IO.FS.writeFile (temporary / "modules.list") (String.join (modules.toList.map fun r => col r 1 ++ "\n"))
      let source := "module\n" ++ String.join (modules.toList.map fun r => "public import " ++ col r 1 ++ "\n") ++
        "public meta import Checker.Vocabulary\n\n#vocabulary_dump " ++ (toJson (temporary / "modules.list").toString).compress ++
        " " ++ (toJson (temporary / "environment.tsv").toString).compress ++ "\n"
      IO.FS.writeFile (temporary / "VocabularyRun.lean") source
      lean project temporary compiler (temporary / "VocabularyRun.lean")
        #["--root=" ++ temporary.toString,"-o",(temporary / "VocabularyRun.olean").toString]
        #[("LEAN_PATH",some (temporary.toString ++ ":" ++ semantic.toString ++ ":" ++ trim (← output project "lake" #["env","printenv","LEAN_PATH"])))]
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
def skeletonCoverage (progress claims bindings : Array Row) : IO Unit := diagnosticPass "source skeleton coverage failed" fun record => do
  let complete := indexBy progress 1; let known := indexBy claims 1
  for claim in claims do
    if #["skeleton_frozen","proof_active","complete"].contains (col (complete[col claim 2]?.getD #[]) 2) &&
        col claim 12 == "false" && col claim 6 != "out_of_scope" then
      record (bindings.any (col · 1 == col claim 1)) s!"skeleton source lacks a binding {col claim 1}"
  for binding in bindings do
    record ((bindings.filter (col · 1 == col binding 1)).size == 1)
      s!"duplicate binding {col binding 1}"
  for source in progress do
    if #["skeleton_frozen","proof_active","complete"].contains (col source 2) then
      let count := bindings.filter fun b => col (known[col b 1]?.getD #[]) 2 == col source 1
      let targets := claims.filter fun c => col c 2 == col source 1 && col c 12 == "false" && col c 6 != "out_of_scope"
      record (count.size == targets.size) s!"binding count does not match formalization targets in {col source 1}"

/-- Match every expected statement, proof and axiom to exactly the observed module declaration. -/
def skeletonDeclarations (bindings axioms actual : Array Row) : IO Unit := do
  let errors ← IO.mkRef (#[] : Array String)
  let record := fun (valid : Bool) (message : String) => do
    unless valid do errors.modify (·.push message)
  let mut expected : Std.HashMap (String × String) Row := {}
  for row in bindings do
    let mut entries := #[#[col row 4,col row 2,col row 5,col row 7,col row 8,"statement",col row 1,col row 6]]
    if col row 3 != "NONE" then entries := entries.push #[col row 4,col row 3,col row 10,col row 11,col row 12,"proof",col row 1,col row 6]
    if col row 13 != "NONE" then entries := entries.push #[col row 4,col row 13,"theorem",col row 14,"NONE","nonvacuity",col row 1,col row 6]
    for declaration in entries do
      let key := (col declaration 1,col declaration 2)
      record (!expected.contains key) s!"duplicate registered declaration {key.2}"
      expected := expected.insert key declaration
  for row in axioms do
    let key := (col row 3,col row 2)
    record (!expected.contains key) s!"duplicate registered declaration {key.2}"
    expected := expected.insert key #[key.1,key.2,"axiom",col row 8,"NONE","axiom",col row 1,"axiom"]
  let mut observed : Std.HashSet (String × String) := {}
  for row in actual do
    let key := (col row 1,col row 2)
    observed := observed.insert key
    let some expectedRow := expected[key]? | do
      errors.modify (·.push s!"extra declaration {key.2}")
      continue
    record (col expectedRow 3 == col row 3) s!"wrong declaration kind {key.2} expected={col expectedRow 3} actual={col row 3}"
    record (col expectedRow 4 == "PENDING" || col expectedRow 4 == col row 4) s!"wrong type OID {key.2}"
    record (#["NONE","PENDING"].contains (col expectedRow 5) || col expectedRow 5 == col row 5) s!"wrong value OID {key.2}"
  for (key,_) in expected do
    record (observed.contains key) s!"missing or wrong-module declaration {key.1}\x1c{key.2}"

  let failures ← errors.get
  require failures.isEmpty (String.intercalate "\n" failures.toList ++ "; declaration registry/environment mismatch")

/-- Preserve exact primary propositions, proof types, nonvacuity and direct-hole ownership. -/
def skeletonShapes (bindings actual : Array Row) : IO Unit := diagnosticPass "primary/proof-hole bijection failed" fun record => do
  let statements := indexBy bindings 2; let proofs := indexBy (bindings.filter (col · 3 != "NONE")) 3
  let nonvacuity := indexBy (bindings.filter (col · 13 != "NONE")) 13
  for row in actual do
    let name := col row 2; let direct := (col row 7).toNat?.getD 0; let transitive := col row 8 == "true"
    if let some binding := statements[name]? then
      record (direct == 0 && !transitive) s!"primary statement depends on sorryAx {name}"
      record (col row 14 != "true") s!"literal True primary statement {name}"
      record (col binding 6 != "proof_proposition" || col row 15 == "true") s!"proof proposition is not Prop-valued {name}"
    else if let some binding := proofs[name]? then
      record (col row 6 == "true") s!"proof declaration is not Prop-valued {name}"
      record (col row 18 == col binding 2) s!"proof type is not exactly the bound primary statement {name} expected={col binding 2} actual={col row 18}"
      if col binding 12 == "NONE" then
        record (direct == 1 && transitive) (if direct == 0 && transitive then
          s!"hidden or transitive-only sorryAx {name}" else
          s!"proof stub needs exactly one direct sorryAx {name}")
      else record (direct == 0 && !transitive) s!"completed proof depends on sorryAx {name}"
    else if let some binding := nonvacuity[name]? then
      record (direct == 0 && !transitive) s!"nonvacuity declaration depends on sorryAx {name}"
      record (col row 16 != "true") s!"nonvacuity declaration concludes True {name}"
      record (col row 17 != "true") s!"nonvacuity declaration follows from its own hypotheses {name}"
      record ((col row 9).splitOn "," |>.contains (col binding 2)) s!"nonvacuity declaration does not reference its bound statement {name}"
    else record (direct == 0 && !transitive) s!"unregistered sorryAx declaration {name}"

/-- Actual setup uses must be earlier and admitted, with assumption context occurring in binders. -/
def skeletonContext (claims bindings vocabulary contexts dependencies modules actual : Array Row) : IO Unit := diagnosticPass "claim-context semantic mismatch" fun record => do
  let sequence : Std.HashMap String Nat := (claims.zipIdx).foldl (fun result (row,i) => result.insert (col row 1) (i+1)) {}
  let claimOf := indexBy bindings 2
  let registered : Std.HashSet String := (bindings ++ vocabulary).foldl (fun result row => result.insert (col row 2)) {}
  let rootOf := fun name : String => (name.splitOn ".").head!
  let projects : Std.HashSet String := modules.foldl (fun result row => result.insert (rootOf (col row 1))) {}
  let mut admitted : Std.HashSet (String × String) := {}; let mut forward : Std.HashSet (String × String) := {}
  let mut context : Std.HashSet (String × String) := {}; let mut assumptions : Std.HashSet (String × String) := {}
  for row in contexts do
    let edge := (col row 1,col row 3)
    admitted := admitted.insert edge; context := context.insert edge
    if col row 4 == "assumption" then assumptions := assumptions.insert edge
  for row in dependencies do
    let edge := if col row 2 == "required_by" then (col row 3,col row 1) else (col row 1,col row 3)
    admitted := admitted.insert edge
    if col row 2 == "required_by" then forward := forward.insert edge
  let mut used : Std.HashSet (String × String) := {}; let mut guards : Std.HashSet (String × String) := {}
  for row in actual do
    if let some owner := claimOf[col row 2]? then
      let claim := col owner 1
      for name in (col row 9 ++ "," ++ col row 10).splitOn "," do
        if name.isEmpty then continue
        if let some setup := claimOf[name]? then
          if col setup 1 != claim then used := used.insert (claim,col setup 1)
        record (!projects.contains (rootOf name) || name == col row 2 || registered.contains name)
          s!"primary statement uses an unregistered project constant {name}"
      for name in (col row 12 ++ "," ++ col row 13).splitOn "," do
        if let some setup := claimOf[name]? then guards := guards.insert (claim,col setup 1)
  for edge in context do
    record (used.contains edge) s!"registered context is absent from statement {edge.1}\x1c{edge.2}"
    record (!assumptions.contains edge || guards.contains edge) s!"assumption context is not a binder or antecedent {edge.1}\x1c{edge.2}"
  for edge in used do
    if !admitted.contains edge then
      record false s!"actual setup reference lacks claim-context or dependency {edge.1}\x1c{edge.2}"
    else if forward.contains edge then
      record (sequence[edge.2]?.getD 0 > sequence[edge.1]?.getD 0) s!"required_by reference does not pull a later claim forward {edge.1}\x1c{edge.2}"
    else record (sequence[edge.2]?.getD 0 < sequence[edge.1]?.getD 0) s!"statement references a claim that is not earlier {edge.1}\x1c{edge.2}"

/-- Vocabulary use is checked per primary claim, independently of the global declaration registry. -/
def skeletonVocabulary (vocabulary bindings admissions reviews actual : Array Row) : IO Unit := diagnosticPass "claim vocabulary admission mismatch" fun record => do
  let vocabularyByName := indexBy vocabulary 2; let owners := indexBy bindings 2; let basis := indexBy reviews 1
  for row in actual do
    if let some binding := owners[col row 2]? then
      let owner := col binding 1
      for name in (col row 9 ++ "," ++ col row 10).splitOn "," do
        if let some declaration := vocabularyByName[name]? then
          if col (basis[owner]?.getD #[]) 2 != "project_vocabulary" then
            record false s!"primary project vocabulary contradicts claim review basis {owner} {col declaration 1}"
          else
            record (admissions.any fun a => col a 1 == owner && col a 2 == col declaration 1)
              s!"primary vocabulary use lacks claim-vocabulary admission {owner} {col declaration 1}"

/-- Actual nonstandard kernel dependencies exactly match approved claim-to-axiom relations. -/
def skeletonAxioms (bindings axioms approved actual : Array Row) : IO Unit := diagnosticPass "claim axiom contract failed" fun record => do
  let mut owners : Std.HashMap String String := {}
  for row in bindings do
    owners := owners.insert (col row 2) (col row 1)
    if col row 3 != "NONE" then owners := owners.insert (col row 3) (col row 1)
    if col row 13 != "NONE" then owners := owners.insert (col row 13) (col row 1)
  let axiomByName := indexBy axioms 2
  let mut uses : Std.HashSet (String × String) := {}; let mut used : Std.HashSet String := {}
  for row in actual do
    if let some owner := owners[col row 2]? then
      for name in (col row 11).splitOn "," do
        if let some registeredAxiom := axiomByName[name]? then
          uses := uses.insert (owner,col registeredAxiom 1); used := used.insert (col registeredAxiom 1)
        else
          record (#["","propext","Classical.choice","Quot.sound","sorryAx"].contains name) s!"unregistered nonstandard axiom {name} used by {col row 2}"
  for edge in approved do
    record (uses.contains (col edge 1,col edge 2)) "approved claim axiom is not used"
  for edge in uses do
    record (approved.any fun r => (col r 1,col r 2) == edge) "unapproved claim axiom is used"
  for registeredAxiom in axioms do record (used.contains (col registeredAxiom 1)) s!"registered axiom is unused {col registeredAxiom 1}"

/-- Reachability isolates unresolved statements from the default mathematical root. -/
def skeletonIsolation (vocabulary statements imports : Array Row) : IO Unit := diagnosticPass "skeleton import isolation failed" fun record => do
  let reach := reachability (vocabulary ++ statements) imports
  let umbrellas := statements.filter (col · 3 != "leaf")
  record (umbrellas.size == 1) "skeleton needs exactly one umbrella"
  let root := (vocabulary.filter (col · 3 == "root")).back?.map (col · 1) |>.getD ""
  for row in statements do
    if col row 3 == "leaf" then record (reach.contains (((umbrellas.back?).map (col · 1)).getD "",col row 1)) s!"umbrella misses {col row 1}"
    record (root.isEmpty || !reach.contains (root,col row 1)) s!"production root reaches {col row 1}"

/-- Only one declaration-local warning exception belongs to each registered unresolved proof. -/
def skeletonWarnings (bindings : Array Row) (environment : String) : IO Unit := do
  diagnosticPass "warning exception ownership failed" fun record => do
    let expected : Std.HashSet (String × String) := bindings.foldl (fun result row =>
      if col row 9 == "proof_stub" && col row 12 == "NONE" then result.insert (col row 4,col row 3) else result) {}
    let mut seen : Std.HashMap (String × String) Nat := {}
    for line in lines environment do
      let row := split line "\t"
      if col row 1 == "W" then
        let key := (col row 2,col row 3)
        if col row 4 != "declaration" || key.2 == "NONE" then
          record false s!"unscoped warningAsError suppression in {key.1}"
        else if !expected.contains key then
          record false s!"warningAsError exception is not a registered unresolved proof {key.2}"
        else seen := seen.insert key (seen[key]?.getD 0 + 1)
    for key in expected do
      record (seen[key]?.getD 0 == 1) s!"unresolved proof needs exactly one declaration-local warningAsError exception {key.1}\x1c{key.2}"
  diagnosticPass "diagnostic suppression policy failed" fun record => do
    for line in lines environment do
      let row := split line "\t"
      record (col row 1 != "S") s!"forbidden diagnostic suppression {col row 3} in {col row 2}"

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
      let semantic ← prepareChecker project checker temporary compiler "Skeleton"
      let vocabulary ← table target "modules"; let modules := vocabulary ++ statements
      let vocabularyImports ← table target "imports"; let statementImports ← table target "statement-imports"
      compileModules project target temporary compiler semantic modules (vocabularyImports ++ statementImports)
      for (file,rows) in #[("modules.list",modules),("statement-modules.list",statements)] do
        IO.FS.writeFile (temporary / file) (String.join (rows.toList.map fun r => col r 1 ++ "\n"))
      let imports := String.join (modules.toList.map fun row => "import " ++ col row 1 ++ "\n")
      let quoted := fun path : FilePath => (toJson path.toString).compress
      IO.FS.writeFile (temporary / "SkeletonRun.lean") (imports ++ "import Checker.Skeleton\n\n#skeleton_dump " ++
        quoted (temporary / "statement-modules.list") ++ " " ++ quoted (temporary / "environment.tsv") ++
        " " ++ quoted target ++ " " ++ quoted (target / "registry/statement-modules.tsv") ++ "\n")
      let search := temporary.toString ++ ":" ++ semantic.toString ++ ":" ++ trim (← output project "lake" #["env","printenv","LEAN_PATH"])
      lean project temporary compiler (temporary / "SkeletonRun.lean")
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
        lean project temporary compiler isolationSource
          #["-DwarningAsError=true","--root=" ++ project.toString,"-o",(semantic / "Checker/LakeIsolation.olean").toString]
          #[("LEAN_PATH",some search)]
        require (trim (← git project #["hash-object",isolationSource.toString]) == isolationBefore)
          "Lake isolation checker source changed during compilation"
        IO.FS.writeFile (temporary / "LakeIsolationRun.lean") (imports ++
          "import Checker.LakeIsolation\n#eval Checker.LakeIsolation.check " ++ quoted target ++ "\n")
        lean project temporary compiler (temporary / "LakeIsolationRun.lean") #[] #[("LEAN_PATH",some search)]
        runGate target ⟨"lake",#["build","+LatticeSystem.Skeleton"]⟩
      IO.println "check-skeleton: ok"
  catch error => throw <| IO.userError s!"check-skeleton: {error}"

end Checker.SemanticDriver
