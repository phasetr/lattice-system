import Checker.Regressions

/-! Actual reader projections and independently authenticated producer identities. -/
namespace Checker.CheckAll
open Lean System

/-- Current receipt encoding; older dispatcher receipts are never cache evidence. -/
def version : Nat := 4
/-- The sole regression-suite definition. -/
def suites : Array (String × String) := Checker.Regressions.groups.map fun group => (group.name,group.name)
/-- Registries whose semantic changes require fresh PR regressions. -/
def semanticTables := #["phase", "source-progress", "bindings", "dependencies", "claim-context",
  "axioms", "claim-axioms", "vocabulary", "claim-vocabulary", "modules", "imports",
  "statement-modules", "statement-imports"]
/-- Known corpus-only tables; unknown paths are never silently light. -/
def corpusTables := #["tracks", "sources", "source-invariants", "pages", "claims", "source-items",
  "item-claims", "slices", "claim-vocabulary-review", "correction-events",
  "claim-normalization-reviews", "claim-corrections", "claim-successors",
  "source-item-additions", "claim-content-amendments"]
/-- Policy documents are projected through the exact predicates their checker reads. -/
def policyPaths := #["README.md", "DESIGN.md", ".github/pull_request_template.md"]
/-- Executable/fixture overrides are forbidden on the production CI route. -/
def overrides := #["CHECK_BASE_DIFF", "CHECK_CORRECTIONS", "GENERATE_PUBLIC_DOCS", "LATTICE_TEST_ROOT",
  "LATTICE_SEMANTIC_CACHE", "LATTICE_SKELETON_CHECKER_DIR", "LATTICE_SKELETON_ACTUAL_OUT", "PYTHONOPTIMIZE", "PYTHONPATH",
  "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS", "ELAN_TOOLCHAIN", "BASH_ENV", "ENV",
  "GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM", "GIT_CONFIG_PARAMETERS",
  "LATTICE_CHECK_ALL_EXEC", "LATTICE_CHECK_ALL_PROJECT", "LEAN_CC", "LEAN_CFLAGS", "LEAN_LDFLAGS",
  "CC", "CFLAGS", "LDFLAGS", "CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "LIBRARY_PATH",
  "SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "CLANG_CONFIG_FILE_SYSTEM_DIR", "CLANG_CONFIG_FILE_USER_DIR"]
/-- Receipt marker occurs exactly once in a successful producing job. -/
def marker := "rewrite-ci-receipt: "

/-- Resolve and validate a required commit. -/
def commit (root : System.FilePath) (ref : String) : IO String := do
  let s := trim (← git root #["rev-parse", "--verify", ref ++ "^{commit}"])
  require (hex s 40) "invalid commit"
  pure s
/-- Read exact commit parent identities. -/
def parents (root : System.FilePath) (ref : String) : IO (Array String) := do
  pure <| (split (trim (← git root #["show", "-s", "--format=%P", ref])) " ").filter (!·.isEmpty)
/-- Read the immutable tree identity. -/
def tree (root : System.FilePath) (ref : String) : IO String := do
  pure <| trim (← git root #["rev-parse", ref ++ "^{tree}"])
/-- Hash canonical Lean JSON using the already-used host SHA256 utility. -/
def digest (root : System.FilePath) (j : Json) : IO String := do
  let result ← output root "shasum" #["-a", "256"] (some j.compress)
  let hash := (split (trim result) " ")[0]!
  require (hex hash 64) "SHA256 operation failed"
  pure hash
/-- Git inventory entry, independent of receipt claims. -/
structure Entry where
  /-- Tracked path. -/
  path : String
  /-- Git mode, preserving type and executable changes. -/
  mode : String
  /-- Git object kind. -/
  kind : String
  /-- Immutable object identity. -/
  oid : String
  deriving Inhabited
/-- Read complete tracked file/type/mode inventory. -/
def entries (root : System.FilePath) (ref : String) : IO (Array Entry) := do
  let raw ← git root #["ls-tree", "-r", "-z", ref]
  let mut result := #[]
  for record in split raw "\u0000" do
    if record.isEmpty then continue
    let pair := split record "\t"
    require (pair.size == 2) "invalid Git tree entry"
    let metadata := split pair[0]! " "
    require (metadata.size == 3) "invalid Git tree metadata"
    result := result.push ⟨pair[1]!, metadata[0]!, metadata[1]!, metadata[2]!⟩
  pure result
/-- Registry/docs/policy projections are distinct from executable bytes. -/
def projected (p : String) : Bool := p.startsWith "registry/" || p.startsWith "docs/" || policyPaths.contains p
/-- Independently compute executable/configuration identity. -/
def engine (root : System.FilePath) (rows : Array Entry) : IO String :=
  digest root <| Json.mkObj <| (rows.filter (!projected ·.path)).toList.map fun e =>
    (e.path, toJson #[e.mode, e.kind, e.oid])
/-- Policy projection binds exactly the current reader's meaningful predicates. -/
def policyProjection (path text : String) : Json := Json.mkObj <|
  [("exact_pr", toJson (decide ((text.splitOn "exact PR").length > 1))),
   ("exact_head", toJson (decide ((text.splitOn "exact head SHA").length > 1)))] ++
  if path == ".github/pull_request_template.md" then
    [("unchecked", toJson (decide ((text.splitOn "- [ ] USER ONLY").length > 1))),
     ("checked", toJson ((decide ((text.splitOn "- [x] USER ONLY").length > 1)) ||
                        (decide ((text.splitOn "- [X] USER ONLY").length > 1))))] else []
/-- Require available immutable historical fixture objects, not a shallow-clone guess. -/
def historical (root : System.FilePath) (ref : String) : IO Json := do
  let events ← git root #["show", ref ++ ":registry/correction-events.tsv"]
  let mut ids := #["c6fb1ec6046626e14dd9a65f396a66386fcb9b7b", "cf4a289e7c766554c8821e167eddac2c3e291c2a"]
  for line in (split events "\n").toList.drop 1 do
    let row := split line "\t"
    if row.size ≥ 4 && !ids.contains row[3]! then ids := ids.push row[3]!
  let mut result := []
  for id in ids do
    let resolved ← commit root id
    let objects := (← entries root resolved).filter (·.path.startsWith "registry/")
    let checked ← output root "git" #["cat-file", "--batch-check"]
      (some (String.join (objects.toList.map (·.oid ++ "\n"))))
    let lines := (split checked "\n").filter (!·.isEmpty)
    require (lines.size == objects.size && lines.all fun s =>
      let fields := split s " "; fields.size == 3 && fields[1]! == "blob") "historical fixture missing"
    result := (id, toJson (← tree root resolved)) :: result
  pure <| Json.mkObj result

/-- Known infrastructure files are selected by their readers, rather than a global engine-change veto. -/
def knownPath (path : String) : Bool :=
  path == ".gitignore" || path.startsWith "docs/" || policyPaths.contains path ||
  path == "LatticeSystem.lean" || (path.startsWith "LatticeSystem/" && path.endsWith ".lean") ||
  #[".github/CODEOWNERS",".github/workflows/rewrite-ci.yml","Checker/CheckAll.lean","Checker/Inputs.lean"].contains path ||
  Checker.Regressions.commonInputs.contains path ||
  Checker.Regressions.groups.any (fun group => group.inputs.contains path) ||
  (path.startsWith "registry/" && path.endsWith ".tsv" &&
    (semanticTables ++ corpusTables).contains (((path.drop 9).toString.dropEnd 4).toString))

/-- Destructive or unknown differences retain the conservative full-regression fallback. -/
def changeForcesFull (path status oldMode newMode : String) (headerChanged : Bool) : Bool :=
  status != "M" || oldMode != newMode || !#["100644","100755"].contains newMode ||
    !knownPath path || headerChanged

/-- Every raw NUL endpoint is inspected, including both sides of renames represented as delete/add. -/
def fullRequired (root : FilePath) (base head : String) : IO Bool := do
  let raw := split (← git root #["diff","--raw","--no-renames","--no-abbrev","-z",base,head]) "\x00"
  require (raw.size > 0 && raw.back! == "") "invalid raw Git difference terminator"
  let mut full := false
  require ((raw.size - 1) % 2 == 0) "invalid raw Git difference arity"
  for i in [:(raw.size-1)/2] do
    let fields := split raw[i*2]! " "
    require (fields.size == 5) "invalid raw Git difference"
    let path := raw[i*2+1]!
    let mut changedHeader := false
    if fields[4]! == "M" && path.startsWith "registry/" && path.endsWith ".tsv" then
      changedHeader := (split (← git root #["show",base ++ ":" ++ path]) "\n")[0]! !=
        (split (← git root #["show",head ++ ":" ++ path]) "\n")[0]!
    full := full || changeForcesFull path fields[4]! (fields[0]!.drop 1).toString fields[1]! changedHeader
  return full

/-- A deterministic set avoids duplicated reader entries and duplicate JSON fields. -/
def distinctPaths (paths : Array String) : Array String :=
  (paths.foldl (fun result path => if result.contains path then result else result.push path) #[]).qsort (· < ·)

/-- Convert one actual Git entry to a mode/type/content tuple without exposing source bytes. -/
def entryValue (entry : Entry) : Json := toJson #[entry.mode,entry.kind,entry.oid]

/-- Hash only a group's explicit imports and actual runtime routes, independently of the producer engine. -/
def payloads (root : FilePath) (rows : Array Entry)
    (headers registry policy history environment : Json) (production : Json := Json.mkObj []) : IO (Json × String) := do
  let executable ← engine root rows
  let mut signatures := []
  for group in Checker.Regressions.groups do
    let paths := distinctPaths (Checker.Regressions.commonInputs ++ group.inputs)
    let inputs := Json.mkObj <| paths.toList.map fun path =>
      (path, (rows.find? (·.path == path)).map entryValue |>.getD Json.null)
    let mut fields := [("version",toJson version),("group",toJson group.name),
      ("environment",environment),("inputs",inputs)]
    if group.corpus then fields := ("registry",registry) :: fields
    if group.headers then fields := ("headers",headers) :: fields
    if group.policy then fields := ("policy",policy) :: fields
    if group.history then fields := ("history",history) :: fields
    if group.production then fields := ("production",production) :: fields
    if group.layout then fields := ("layout",Json.mkObj (rows.toList.map fun entry =>
      (entry.path,toJson #[entry.mode,entry.kind]))) :: fields
    signatures := (group.name,toJson (← digest root (Json.mkObj fields))) :: signatures
  return (Json.mkObj signatures,executable)

/-- Resolve every real production file read by the production-derived vocabulary counterfactual. -/
def registeredProduction (root : FilePath) (ref : String) (rows : Array Entry) : IO Json := do
  let text ← git root #["show",ref ++ ":registry/modules.tsv"]
  let mut files := []
  for line in (split text "\n").toList.drop 1 do
    if line.isEmpty then continue
    let row := split line "\t"
    require (row.size == 3) "invalid production module input"
    let path := row[1]!
    require (!path.startsWith "/" && !path.contains '\x00' &&
      !(path.splitOn "/").contains ".." && path.endsWith ".lean") "unsafe production module input"
    let some entry := rows.find? (·.path == path) | throw <| IO.userError "missing production module input"
    require (entry.kind == "blob" && #["100644","100755"].contains entry.mode) "invalid production module input type"
    files := (path,entryValue entry) :: files
  return Json.mkObj files

/-- Establish each current group's closed actual inputs; missing required files fail into full execution. -/
def signatures (root : FilePath) (ref : String) (environment : Json) : IO (Json × String) := do
  let rows ← entries root ref
  for group in Checker.Regressions.groups do
    for path in distinctPaths (Checker.Regressions.commonInputs ++ group.inputs) do
      let some entry := rows.find? (·.path == path) | throw <| IO.userError "missing regression source input"
      require (entry.kind == "blob" && #["100644","100755"].contains entry.mode) "unsupported regression source type"
  let mut headers := []; let mut registry := []; let mut policy := []
  for entry in rows do
    require (entry.kind == "blob") "non-blob tracked input"
    if entry.path.startsWith "registry/" then
      let text ← git root #["show",ref ++ ":" ++ entry.path]
      headers := (entry.path,toJson (split text "\n")[0]!) :: headers
      registry := (entry.path,entryValue entry) :: registry
    if policyPaths.contains entry.path then
      policy := (entry.path,policyProjection entry.path (← git root #["show",ref ++ ":" ++ entry.path])) :: policy
  payloads root rows (Json.mkObj headers) (Json.mkObj registry) (Json.mkObj policy)
    (← historical root ref) environment (← registeredProduction root ref rows)

/-- Exactly the authorized, nondefault checker targets can be excluded from the mathematical configuration. -/
def checkerLakeSuffix : String := "\n# Verification infrastructure is an explicit target, separate from the mathematical default.\n[[lean_lib]]\nname = \"Checker\"\n\n[[lean_exe]]\nname = \"checker\"\nroot = \"Checker.Main\"\n"

/-- Preserve the mathematical package/configuration prefix byte-for-byte; unknown tooling config is not light. -/
def mathematicalLake (text : String) : IO String := do
  let marker := "\n# Verification infrastructure is an explicit target, separate from the mathematical default."
  let parts := split text marker
  if parts.size == 1 then
    require ((text.splitOn "name = \"Checker\"").length == 1 &&
      (text.splitOn "name = \"checker\"").length == 1) "unknown checker Lake configuration"
    return text
  require (parts.size == 2 && text.endsWith checkerLakeSuffix) "unknown checker Lake suffix"
  return ((text.dropEnd checkerLakeSuffix.length).toString)

/-- Select the actual mathematical build sources and dependency/configuration inputs. -/
def mathematicalPath (path : String) : Bool :=
  path == "LatticeSystem.lean" || (path.startsWith "LatticeSystem/" && path.endsWith ".lean") ||
  #["lean-toolchain","lake-manifest.json","registry/modules.tsv","registry/imports.tsv"].contains path

/-- A mathematical projection records every path, mode, kind and content, including the canonical Lake prefix. -/
def mathematicalInputs (root : FilePath) (ref : String) : IO String := do
  let rows ← entries root ref
  require (!(rows.any (fun entry => entry.path == "lakefile.lean"))) "unknown effective mathematical configuration"
  let mut fields := []
  for entry in rows.filter (mathematicalPath ·.path) do
    require (entry.kind == "blob" && #["100644","100755"].contains entry.mode) "unsupported mathematical input type"
    fields := (entry.path,entryValue entry) :: fields
  for path in #["LatticeSystem.lean","lean-toolchain","lake-manifest.json","registry/modules.tsv","registry/imports.tsv"] do
    require (rows.any (·.path == path)) "missing mathematical input"
  let some lake := rows.find? (·.path == "lakefile.toml") | throw <| IO.userError "missing mathematical configuration"
  require (lake.kind == "blob" && #["100644","100755"].contains lake.mode) "invalid mathematical configuration type"
  let configuration ← mathematicalLake (← git root #["show",ref ++ ":lakefile.toml"])
  digest root (Json.mkObj (("lakefile.toml",toJson #[lake.mode,lake.kind,configuration]) :: fields))

/-- Build selection is independent of unrelated regression-engine changes. -/
structure BuildSelection where
  required : Bool := true
  reason : String := "mathematical inputs unavailable"
  before : String := ""
  after : String := ""

/-- Unknown projection establishes no equality and conservatively requests the mathematical build. -/
def selectBuild (root : FilePath) (base head : String) : IO BuildSelection := do
  try
    let before ← mathematicalInputs root base
    let after ← mathematicalInputs root head
    return ⟨before != after,if before == after then "mathematical inputs unchanged" else "mathematical inputs changed",before,after⟩
  catch _ => return {}

/-- Local gates consume working files: dirty mathematical inputs cannot borrow immutable-HEAD equality. -/
def selectLocalBuild (root : FilePath) (base head : String) : IO BuildSelection := do
  let selected ← selectBuild root base head
  if selected.required then return selected
  try
    let raw := split (← git root #["diff","--raw","--no-renames","--no-abbrev","-z","HEAD"]) "\x00"
    require (raw.size > 0 && raw.back! == "" && (raw.size-1)%2 == 0) "invalid local mathematical difference"
    for i in [:(raw.size-1)/2] do
      let fields := split raw[i*2]! " "
      require (fields.size == 5) "invalid local mathematical difference"
      let path := raw[i*2+1]!
      if mathematicalPath path || path == "lakefile.lean" then
        return {selected with required := true,reason := "uncommitted mathematical input change"}
      if path == "lakefile.toml" then
        require (fields[4]! == "M" && (fields[0]!.drop 1).toString == fields[1]! && fields[1]! == "100644")
          "mathematical configuration mode or identity changed"
        let metadata ← (root / path).symlinkMetadata
        require (metadata.type == .file) "nonregular mathematical configuration"
        let before ← mathematicalLake (← git root #["show",head ++ ":" ++ path])
        let after ← mathematicalLake (← IO.FS.readFile (root / path))
        if before != after then return {selected with required := true,reason := "uncommitted mathematical configuration change"}
    let untracked ← git root #["ls-files","--others","--exclude-standard","-z","--",
      "LatticeSystem.lean","LatticeSystem","lakefile.lean","lakefile.toml","lean-toolchain","lake-manifest.json",
      "registry/modules.tsv","registry/imports.tsv"]
    require untracked.isEmpty "untracked mathematical input"
    return selected
  catch _ => return {selected with required := true,reason := "working mathematical inputs unavailable"}

end Checker.CheckAll
