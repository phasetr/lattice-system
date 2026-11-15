import Lean

/-!
Shared current-tree and regression dispatcher. Source mathematics stays in the
registered production modules; this program controls verification and evidence.
-/

open Lean

namespace Checker.CheckAll

/-- Current receipt encoding; older dispatcher receipts are never cache evidence. -/
def version : Nat := 3
/-- The sole regression-suite definition. -/
def suites : Array (String × String) := #[
  ("checkers", "test-checkers.sh"), ("skeleton", "test-skeleton-semantic.sh"),
  ("corrections", "test-claim-corrections-runtime.sh"),
  ("content", "test-content-amendments-runtime.sh"), ("selector", "test-base-diff-ci-runtime.sh")]
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
  "LATTICE_SKELETON_CHECKER_DIR", "LATTICE_SKELETON_ACTUAL_OUT", "PYTHONOPTIMIZE", "PYTHONPATH",
  "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS", "ELAN_TOOLCHAIN", "BASH_ENV", "ENV",
  "GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM", "GIT_CONFIG_PARAMETERS",
  "LATTICE_CHECK_ALL_EXEC", "LATTICE_CHECK_ALL_PROJECT", "LEAN_CC", "LEAN_CFLAGS", "LEAN_LDFLAGS",
  "CC", "CFLAGS", "LDFLAGS", "CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "LIBRARY_PATH",
  "SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "CLANG_CONFIG_FILE_SYSTEM_DIR", "CLANG_CONFIG_FILE_USER_DIR"]
/-- Receipt marker occurs exactly once in a successful producing job. -/
def marker := "rewrite-ci-receipt: "

/-- Fail without exposing captured HTTP bodies, headers or secret values. -/
def require (b : Bool) (message : String) : IO Unit := unless b do throw <| IO.userError message
/-- Trim command terminators without interpreting contents. -/
def trim (s : String) : String := s.trimAscii.toString
/-- Preserve NUL-separated Git paths, including rename endpoints as add/delete. -/
def split (s sep : String) : Array String := (s.splitOn sep).toArray
/-- Validate a fixed-width lowercase hexadecimal identifier. -/
def hex (s : String) (n : Nat) : Bool := s.length == n && s.toList.all fun c =>
  c.isDigit || ('a' ≤ c && c ≤ 'f')
/-- Read a required JSON field with a bounded diagnostic. -/
def field (j : Json) (k : String) : IO Json := IO.ofExcept <| j.getObjVal? k
/-- Read a required JSON string. -/
def str (j : Json) (k : String) : IO String := do IO.ofExcept <| (← field j k).getStr?
/-- Read a required JSON natural number. -/
def nat (j : Json) (k : String) : IO Nat := do IO.ofExcept <| (← field j k).getNat?
/-- Read a required JSON array. -/
def arr (j : Json) (k : String) : IO (Array Json) := do IO.ofExcept <| (← field j k).getArr?
/-- Object keys are compared as sets, so extra fields do not pass receipt validation. -/
def keys (j : Json) : Array String := match j with
  | .obj o => o.foldl (fun result k _ => result.push k) #[]
  | _ => #[]
/-- Require precisely the specified object fields. -/
def exactKeys (j : Json) (expected : Array String) : Bool :=
  let actual := keys j
  actual.size == expected.size && expected.all actual.contains
/-- Parse untrusted JSON without echoing its contents on failure. -/
def parse (s : String) : IO Json := match Json.parse s with
  | .ok j => pure j
  | .error _ => throw <| IO.userError "invalid evidence JSON"
/-- Run a thin external operation; sensitive input is supplied through stdin only. -/
def output (root : System.FilePath) (cmd : String) (args : Array String)
    (input : Option String := none) : IO String := do
  let p ← IO.Process.output { cmd, args, cwd := some root } input
  require (p.exitCode == 0) s!"external operation failed: {cmd}"
  pure p.stdout
/-- Read Git data without mutating objects, refs or the working tree. -/
def git (root : System.FilePath) (args : Array String) : IO String := output root "git" args
/-- The closed set of non-generated infrastructure paths; production modules are registry-owned. -/
def fixedTreePaths : Array String := #[
  ".github/CODEOWNERS", ".github/pull_request_template.md", ".github/workflows/rewrite-ci.yml",
  ".gitignore", "DESIGN.md", "LatticeSystem.lean",
  "README.md", "lake-manifest.json", "lakefile.toml",
  "lean-toolchain", "registry/phase.tsv", "registry/tracks.tsv",
  "registry/sources.tsv", "registry/source-invariants.tsv", "registry/source-progress.tsv",
  "registry/pages.tsv", "registry/claims.tsv", "registry/source-items.tsv",
  "registry/item-claims.tsv", "registry/slices.tsv", "registry/dependencies.tsv",
  "registry/bindings.tsv", "registry/axioms.tsv", "registry/claim-axioms.tsv",
  "registry/claim-vocabulary-review.tsv", "registry/vocabulary.tsv", "registry/claim-vocabulary.tsv",
  "registry/modules.tsv", "registry/imports.tsv", "registry/correction-events.tsv",
  "registry/claim-normalization-reviews.tsv", "registry/claim-corrections.tsv", "registry/claim-successors.tsv",
  "registry/source-item-additions.tsv", "registry/claim-content-amendments.tsv", "registry/claim-context.tsv",
  "registry/statement-modules.tsv", "registry/statement-imports.tsv",
  "scripts/check-base-diff.sh", "scripts/check-base-diff-ci.sh",
  "scripts/check-claim-corrections.sh", "scripts/check-content-amendments.py", "scripts/check-vocabulary.sh",
  "scripts/test-base-diff-runtime.sh", "scripts/test-base-diff-ci-runtime.sh", "scripts/test-claim-corrections-runtime.sh",
  "scripts/test-content-amendments-runtime.sh", "scripts/test-checkers.sh", "scripts/test-multisource.sh",
  "scripts/test-tree-policy.sh", "scripts/test-vocabulary-registry.sh", "scripts/test-vocabulary-semantic.sh",
  "scripts/generate-public-docs.py", "scripts/check-skeleton.sh", "scripts/test-skeleton-semantic.sh",
  "docs/index.md", "docs/generated/index.md", "docs/generated/catalog.json",
  "Checker/Semantic.lean", "Checker/Vocabulary.lean", "Checker/Skeleton.lean",
  "Checker/CheckAll.lean"]
/-- Only registered production modules and established generated catalog families extend the closed tree. -/
def allowedTreePath (registered : Array String) (path : String) : Bool :=
  fixedTreePaths.contains path ||
  (#["docs/generated/groups/", "docs/generated/sources/", "docs/generated/tracks/"].any
    (path.startsWith ·) && path.endsWith ".md") ||
  (path.startsWith "LatticeSystem/" && path.endsWith ".lean" && registered.contains path)
/-- Compare whole canonical path components, never a lexical sibling prefix. -/
def pathWithin (path parent : String) : Bool := path == parent || path.startsWith (parent ++ "/")
/-- A fixture tree stays under an external test root that cannot contain the source project. -/
def validateTreeFixture (project root testRoot : String) : IO Unit := do
  require (!pathWithin testRoot project) "LATTICE_TEST_ROOT must be repository-external"
  require (testRoot != "/" && !pathWithin project testRoot) "LATTICE_TEST_ROOT must not contain the repository"
  require (pathWithin root testRoot) "fixture root must be below LATTICE_TEST_ROOT"
/-- Read working registry paths, preserving the header-only bootstrap exception. -/
def treeModules (root : System.FilePath) (fixture : Bool := false) : IO (Array String) := do
  let mut registered := #[]
  if ← (root / "registry/modules.tsv").pathExists then
    let hasStatements ← (root / "registry/statement-modules.tsv").pathExists
    if fixture && !hasStatements then return #[]
    require hasStatements "missing registry/statement-modules.tsv"
    for table in #["modules", "statement-modules"] do
      let text ← IO.FS.readFile (root / "registry" / (table ++ ".tsv"))
      let records := split text "\n"
      let records := if text.endsWith "\n" then records.pop else records
      for line in records.toList.drop 1 do
        let row := split line "\t"
        require (fixture || row.size ≥ 2) "invalid module registry row"
        registered := registered.push (row[1]?.getD "")
  pure registered
/-- Apply closed-path and optional production-module equality checks to an observed live inventory. -/
def validateTreePaths (paths registered : Array String) (production : Bool) : IO Unit := do
  for path in paths do
    require (allowedTreePath registered path) s!"unexpected tracked path: {path}"
  if production && !registered.isEmpty then
    let actual := paths.filter fun p => p == "LatticeSystem.lean" ||
      (p.startsWith "LatticeSystem/" && p.endsWith ".lean")
    require (registered.all actual.contains && actual.all registered.contains)
      "registered modules do not exactly match tracked production Lean sources"
/-- Parse the live Git index, rejecting symbolic links, unresolved stages and ambiguous metadata. -/
def treeIndex (raw : String) : IO (Array String) := do
  let mut paths := #[]
  for record in split raw "\u0000" do
    if record.isEmpty then continue
    let pair := split record "\t"
    require (pair.size == 2) "invalid Git index entry"
    let metadata := split pair[0]! " "
    require (metadata.size == 3 && metadata[2]! == "0" && hex metadata[1]! 40) "invalid or unresolved Git index stage"
    require (metadata[0]! != "120000") "tracked symlink found"
    require (#["100644", "100755"].contains metadata[0]!) "unsupported tracked Git file mode"
    paths := paths.push pair[1]!
  pure paths
/-- Preserve the live closed-tree, fixture isolation, production registry and immutable-pin guards. -/
def checkTree (project target : System.FilePath) (fixture : Bool) : IO Unit := do
  let project ← IO.FS.realPath project
  let root ← IO.FS.realPath target
  if fixture then
    let some testRoot ← IO.getEnv "LATTICE_TEST_ROOT" |
      throw <| IO.userError "fixture mode requires LATTICE_TEST_ROOT"
    let testRoot ← IO.FS.realPath testRoot
    validateTreeFixture project.toString root.toString testRoot.toString
    let tracked ← IO.FS.readFile (root / "tracked-files.txt")
    let paths := (split tracked "\n").filter (!·.isEmpty)
    let registered ← if paths.any (fun p => p.startsWith "LatticeSystem/" && p.endsWith ".lean") then
      treeModules root true else pure #[]
    validateTreePaths paths registered false
    IO.println "check-tree: fixture ok"
    return
  require (trim (← git root #["rev-parse", "--show-toplevel"]) == root.toString)
    "ROOT must be the repository top; fixture mode is explicit"
  let paths ← treeIndex (← git root #["ls-files", "--stage", "-z"])
  validateTreePaths paths (← treeModules root) true
  for pin in #["lean-toolchain", "lake-manifest.json"] do
    let expected := trim (← git root #["rev-parse", "01bcb49d49db92c225cfa74b74d409dd0a9c4edc:" ++ pin])
    require (trim (← git root #["hash-object", pin]) == expected) s!"{pin} differs from legacy anchor"
  IO.println "check-tree: ok"

namespace Registry

/-- Exact table headers are shared by all native data gates. -/
def headers : Array (String × String) := #[
  ("phase", "phase"),
  ("tracks", "track_id\tposition\ttitle\tpublic_slug"),
  ("sources", "source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage"),
  ("source-invariants", "source_id\tphysical_page_count\tactive_claim_count\tformalization_target_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref"),
  ("source-progress", "source_id\tlifecycle\treview_ref"),
  ("pages", "page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid"),
  ("claims", "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref"),
  ("source-items", "item_id\tsource_id\torder_key\tpage_id\titem_kind\tsource_label\ttitle\tlocator\tpublic_group\tpublic_slug\treview_ref"),
  ("item-claims", "item_id\tposition\tclaim_id"),
  ("slices", "slice_id\tposition\tclaim_id"),
  ("dependencies", "claim_id\trole\ttarget_claim_id\trationale"),
  ("bindings", "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref"),
  ("claim-context", "claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref"),
  ("axioms", "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid"),
  ("claim-axioms", "claim_id\taxiom_id"),
  ("claim-vocabulary-review", "claim_id\tbasis\treview_ref"),
  ("vocabulary", "vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope"),
  ("claim-vocabulary", "claim_id\tvocabulary_id"),
  ("modules", "module\tsource_path\trole"),
  ("imports", "module\tposition\timported_module\tis_exported\tis_meta\timport_all"),
  ("correction-events", "event_id\tevent_position\tsource_id\tbase_commit\treview_ref"),
  ("claim-normalization-reviews", "review_id\tevent_id\treview_position\tclaim_id\treview_scope\toutcome\tstatus\trationale\treview_ref"),
  ("claim-corrections", "correction_id\tevent_id\tcorrection_position\treview_id\tclaim_id\taction\told_disposition\told_subkind\tnew_disposition\tnew_subkind"),
  ("claim-successors", "successor_edge_id\tevent_id\tcorrection_id\tpredecessor_claim_id\tsuccessor_position\trelation\tsuccessor_claim_id"),
  ("source-item-additions", "item_addition_id\tevent_id\tcorrection_id\taddition_position\titem_id\treview_ref"),
  ("claim-content-amendments", "amendment_id\tevent_id\tcorrection_id\tclaim_id\told_content_oid\tnew_content_oid\tpage_source_oid\treview_ref"),
  ("statement-modules", "module\tsource_path\trole"),
  ("statement-imports", "module\tposition\timported_module\tis_exported\tis_meta\timport_all")]

/-- A TSV row retains empty terminal fields and exact UTF-8 text. -/
abbrev Row := Array String
/-- One-based source column access, with a missing field kept distinct from a valid row by schema checks. -/
def col (r : Row) (n : Nat) : String := r[n - 1]?.getD ""
/-- Split only record LF, without normalizing CR, BOM or field whitespace. -/
def lines (text : String) : Array String :=
  let result := split text "\n"
  if text.endsWith "\n" then result.pop else result
/-- Parsed working data, including its exact observed row strings. -/
structure Table where
  /-- Header and data records, retaining byte-significant whitespace. -/
  records : Array String := #[]
  /-- Parsed once rather than rebuilt for each foreign-key lookup. -/
  data : Array Row := #[]
  /-- First-column associative lookup, matching the former AWK maps. -/
  byId : Std.HashMap String Row := {}
  /-- The header must have an LF terminator, as required by the former read builtin. -/
  headerEnded : Bool := false
  /-- Shell phase readers required a terminated second record. -/
  secondEnded : Bool := false
  deriving Inhabited
/-- Data rows exclude exactly the header, not blank or malformed rows. -/
def Table.rows (t : Table) : Array Row := t.data
/-- Build the row array and associative index from a single exact byte read. -/
def tableFromText (text : String) : Table := Id.run do
  let records := lines text
  let data := (records.extract 1 records.size).map (split · "\t")
  let mut byId := {}
  for row in data do byId := byId.insert (col row 1) row
  return ⟨records, data, byId, text.contains '\n', (split text "\n").size ≥ 3⟩
/-- A single loading pass shared by native current-data validators. -/
structure Data where
  /-- Working checkout being checked. -/
  root : System.FilePath
  /-- Existing named tables only; missing tables are rejected by their owning gate. -/
  tables : Array (String × Table)
/-- Find a loaded table without treating absence as a valid header. -/
def Data.table (d : Data) (name : String) : Table :=
  ((d.tables.find? (·.1 == name)).map (·.2)).getD {}
/-- Constant-time ID lookup within a parsed table. -/
def Data.row (d : Data) (table id : String) : Row := (d.table table).byId[id]?.getD #[]
/-- Constant-time first-column membership within a parsed table. -/
def Data.has (d : Data) (table id : String) : Bool := (d.table table).byId.contains id
/-- Select an observed source row without scanning the source corpus. -/
def Data.sourceRow (d : Data) (id : String) : Row :=
  d.row (if d.tables.any (·.1 == "sources") then "sources" else "reference") id
/-- A standalone gate cannot turn missing files into an empty valid dataset. -/
def present (d : Data) (names : Array String) : IO Unit :=
  names.forM fun table => require (d.tables.any (·.1 == table)) s!"missing {table}.tsv"
/-- Preserve both read-builtin phase records and the required second LF terminator. -/
def phaseRead (d : Data) : IO Unit := do
  present d #["phase"]
  require (d.table "phase").secondEnded "missing or unterminated phase record"
/-- Whether the modern source registry was actually present. -/
def Data.multi (d : Data) : Bool := d.tables.any (·.1 == "sources")
/-- Select the modern registry or frozen R1/R2 fixture reference. -/
def Data.sources (d : Data) : Array Row := (d.table (if d.multi then "sources" else "reference")).rows
/-- First-column foreign-key existence. -/
def has (rows : Array Row) (id : String) : Bool := rows.any (col · 1 == id)
/-- An exact ASCII digit string, optionally positive without leading zero. -/
def digits (s : String) (positive : Bool := false) : Bool :=
  !s.isEmpty && s.toList.all (fun c => '0' ≤ c && c ≤ '9') && (!positive || !s.startsWith "0")
/-- ASCII letter, independent of locale or Unicode categories. -/
def letter (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
/-- ASCII alphanumeric character. -/
def alnum (c : Char) : Bool := letter c || ('0' ≤ c && c ≤ '9')
/-- Registry review tokens have a nonempty ASCII alphanumeric initial. -/
def token (s : String) : Bool := match s.toList with
  | [] => false
  | c :: rest => alnum c && rest.all (fun c => alnum c || "._:/#@+-".contains c)
/-- Full-string enum membership. -/
def oneOf (s values : String) : Bool := (split values "|").contains s
/-- Frozen Git/content object identifiers admit 40 or 64 lowercase hexadecimal digits. -/
def oid (s : String) : Bool := hex s 40 || hex s 64
/-- Uppercase source identifier. -/
def sourceId (s : String) : Bool := match s.toList with
  | c :: rest => ('A' ≤ c && c ≤ 'Z') && rest.all (fun c => ('A' ≤ c && c ≤ 'Z') || c.isDigit || c == '_')
  | [] => false
/-- Full ASCII namespace component, including Lean apostrophes. -/
def identifier (s : String) : Bool := match s.toList with
  | c :: rest => (letter c || c == '_') && rest.all (fun c => alnum c || c == '_' || c == '\'')
  | [] => false
/-- Nonempty dotted Lean name. -/
def name (s : String) : Bool := (split s ".").all identifier
/-- A project namespace optionally admits its root module. -/
def projectName (s : String) (root : Bool := false) : Bool :=
  (root && s == "LatticeSystem") || (s.startsWith "LatticeSystem." && name s)
/-- Stable IDs have an uppercase namespace and at least four decimal suffix digits. -/
def stableId (s stem : String) (exactFour : Bool := false) : Bool :=
  let parts := split s "-"
  parts.size == 3 && parts[0]! == stem &&
    !parts[1]!.isEmpty && parts[1]!.toList.all (fun c => ('A' ≤ c && c ≤ 'Z') || c.isDigit || c == '_') &&
    digits parts[2]! && (if exactFour then parts[2]!.length == 4 else parts[2]!.length ≥ 4)
/-- Order grammar shared by source-item and modern global-order checks. -/
def orderKey (s : String) : Bool :=
  let parts := split s "."
  parts.size ≥ 2 && parts[0]!.length == 6 && digits parts[0]! &&
    (parts.extract 1 parts.size).all (fun p => p.length == 4 && digits p)
/-- Registry claim grammar deliberately permits at most one appended segment. -/
def claimOrder (s : String) : Bool := orderKey s && (split s ".").size ≤ 3
/-- Canonical lowercase ASCII slug. -/
def slug (s : String) : Bool := !s.isEmpty && (split s "-").all fun p =>
  !p.isEmpty && p.toList.all (fun c => ('a' ≤ c && c ≤ 'z') || c.isDigit)
/-- Match the generator's ASCII slug reduction without Unicode normalization. -/
def slugify (s : String) : String :=
  String.intercalate "-" <| ((split (s.map fun c => if c.toNat < 128 && alnum c then (if 'A' ≤ c && c ≤ 'Z' then c.toLower else c) else '-') "-").filter (!·.isEmpty)).toList
/-- Pad an already-validated decimal value for lexicographic source order. -/
def pad (width : Nat) (s : String) : String := String.ofList (List.replicate (width - s.length) '0') ++ s
/-- Global source tuple, independent of row arrival order. -/
def globalKey (d : Data) (source order : String) : String :=
  let row := d.sourceRow source
  let track := d.row "tracks" (col row 2)
  pad 9 (col track 2) ++ "." ++ pad 9 (col row 3) ++ "." ++ order
/-- C-locale control bytes and the original space/NBSP edge restriction. -/
def validField (s : String) : Bool :=
  !s.toList.any (fun c => c.toNat < 32 || c.toNat == 127) &&
  !s.startsWith " " && !s.endsWith " " && !s.startsWith " " && !s.endsWith " "
/-- Validate an exact table schema before interpreting fields. -/
def schemaTable (d : Data) (table header : String) : IO Unit := do
  let t := d.table table
  require (!t.records.isEmpty && t.headerEnded) s!"missing, empty or unterminated header in {table}.tsv"
  require (t.records[0]! == header) s!"bad header in {table}.tsv"
  let columns := (split header "\t").size
  for record in t.records do
    let row := split record "\t"
    require (row.size == columns) s!"{table}.tsv: expected {columns} columns, got {row.size}"
    require (row.all validField) s!"{table}.tsv: control character or surrounding whitespace in field"
/-- Require unique composite keys; no data row is silently overwritten. -/
def unique (rows : Array Row) (columns : Array Nat) (message : String) : IO Unit := do
  let mut seen : Std.HashSet (Array String) := {}
  for row in rows do
    let key := columns.map (col row)
    require (!seen.contains key) message
    seen := seen.insert key
/-- Require earlier ordering within each owner while allowing unrelated namespaces. -/
def increasing (rows : Array Row) (owner order : Nat) (message : String) : IO Unit := do
  let mut previous : Std.HashMap String String := {}
  for row in rows do
    let id := col row owner; let key := col row order
    if let some old := previous[id]? then require (old < key) message
    previous := previous.insert id key
/-- Validate contiguous positive positions independently for each owner. -/
def contiguous (rows : Array Row) (owner position : Nat) (message : String) : IO Unit := do
  let mut counts : Std.HashMap String Nat := {}
  for row in rows do
    let id := col row owner
    let n := counts[id]?.getD 0 + 1
    require (digits (col row position) true && (col row position).toNat? == some n) message
    counts := counts.insert id n
/-- Kahn elimination detects directed cycles without an unbounded recursive traversal. -/
def acyclic (edges : Array (String × String)) (message : String) : IO Unit := do
  let mut remaining := edges
  for _ in [:edges.size + 1] do
    if remaining.isEmpty then return
    let reduced := remaining.filter fun e => remaining.any (·.2 == e.1)
    require (reduced.size < remaining.size) message
    remaining := reduced
  require remaining.isEmpty message
/-- Retain stage-specific header-only requirements. -/
def emptyTables (d : Data) (tables : Array String) (stem : String) : IO Unit :=
  tables.forM fun table => require ((d.table table).records.size == 1) s!"{stem} header-only {table}.tsv"

/-- Modern source identity, progress and invariant constraints. -/
def sources (d : Data) : IO Unit := do
  present d #["tracks","sources","source-progress","source-invariants"]
  let tracks := (d.table "tracks").rows; let ss := d.sources
  require (!tracks.isEmpty) "no tracks registered"
  unique tracks #[1] "duplicate track ID"; unique tracks #[4] "duplicate track public slug"
  for i in [:tracks.size] do
    let r := tracks[i]!
    require ((col r 1).startsWith "TR-" && sourceId ((col r 1).drop 3).toString) "bad track ID"
    require (digits (col r 2) true && (col r 2).toNat? == some (i + 1)) "track positions are not contiguous"
    require (!(col r 3).isEmpty && slug (col r 4)) "empty track title or bad track public slug"
  require (!ss.isEmpty) "no sources registered"
  unique ss #[1] "duplicate source ID"; unique ss #[5] "duplicate citation key"; unique ss #[13] "duplicate source public slug"
  contiguous ss 2 3 "source positions are not contiguous"
  let mut previous := ""
  for r in ss do
    require (sourceId (col r 1) && d.has "tracks" (col r 2)) "bad source ID or unknown source track"
    require (oneOf (col r 4) "book|paper|preprint|other" && token (col r 5)) "bad source kind or citation key"
    require (!(col r 6).isEmpty && !(col r 7).isEmpty && digits (col r 8) && (col r 8).length == 4 && !(col r 9).isEmpty) "empty source identity or bad source year"
    require (oneOf (col r 10) "isbn|doi|arxiv|none") "bad identifier kind"
    require (if col r 10 == "none" then col r 11 == "NONE" && col r 12 == "NONE" else
      !(col r 11).isEmpty && col r 11 != "NONE" && (col r 12).startsWith "https://") "bad source identifier or public URL"
    require (slug (col r 13) && !(col r 14).isEmpty) "bad source slug or empty local reference key"
    require (((col r 15).isEmpty == (col r 16).isEmpty) && ((col r 15).isEmpty ||
      (oid (col r 15) && oid (col r 16) && (col r 15).length == (col r 16).length))) "source OIDs must transition atomically with equal width"
    require (oneOf (col r 17) "pending|pass1|pass2|reconciled|frozen") "bad source coverage"
    let key := globalKey d (col r 1) ""
    require (previous.isEmpty || previous < key) "sources are not in global track order"
    previous := key
  let progress := (d.table "source-progress").rows
  unique progress #[1] "duplicate source progress"
  for r in progress do
    require (!(d.sourceRow (col r 1)).isEmpty && oneOf (col r 2) "registered|source_frozen|census_pass1|census_pass2|census_reconciled|vocabulary_reviewed|skeleton_frozen|proof_active|complete" && token (col r 3)) "bad source progress"
  require (ss.all fun r => has progress (col r 1)) "source lacks progress row"
  let invariants := (d.table "source-invariants").rows
  unique invariants #[1] "duplicate source invariant"
  for r in invariants do
    require (!(d.sourceRow (col r 1)).isEmpty && digits (col r 2) true && (#[3,4,5,6].all fun n => digits (col r n))) "bad source invariant count or source"
    require ((col r 4).toNat! ≤ (col r 3).toNat! && (col r 6).toNat! ≤ (col r 2).toNat!) "source invariant count exceeds its domain"
    require (oid (col r 7) && token (col r 8)) "bad census OID or invariant review token"

/-- Dependency roles preserve the reviewed reverse-edge meaning of required_by. -/
def dependencies (d : Data) : IO Unit := do
  let deps := (d.table "dependencies").rows
  unique deps #[1,3] "duplicate dependency edge"
  let mut edges := #[]
  for r in deps do
    let a := d.row "claims" (col r 1); let b := d.row "claims" (col r 3)
    require (!a.isEmpty && !b.isEmpty) "unknown dependency claim"
    require (oneOf (col r 2) "requires|required_by|consequence_of") "bad dependency role"
    require (col r 1 != col r 3) "self dependency"
    let ka := if d.multi then globalKey d (col a 2) (col a 3) else col a 3
    let kb := if d.multi then globalKey d (col b 2) (col b 3) else col b 3
    require (kb < ka) (if d.multi then "dependency target is not earlier in global source order" else "dependency target is not earlier in source order")
    require (col r 2 != "required_by" || (col r 4 != "NONE" && !(col r 4).isEmpty)) "required_by needs review rationale"
    if d.multi then
      let sa := d.sourceRow (col a 2); let sb := d.sourceRow (col b 2)
      require (col sa 2 == col sb 2 || (col r 4 != "NONE" && !(col r 4).isEmpty)) "cross-track dependency needs review rationale"
    require (col r 4 == "NONE" || token (col r 4)) "bad dependency rationale token"
    edges := edges.push (if col r 2 == "required_by" then (col r 3,col r 1) else (col r 1,col r 3))
  acyclic edges "dependency cycle"
/-- Full modern page/claim identity and global source order. -/
def order (d : Data) : IO Unit := do
  present d #["tracks","sources","pages","claims","dependencies"]
  for table in #["pages", "claims"] do
    let rows := (d.table table).rows
    increasing rows 2 3 s!"{table} order is not strictly increasing"
    let mut previous := ""
    for r in rows do
      let stem := (if table == "pages" then "PG-" else "CL-") ++ col r 2 ++ "-"
      let suffix := ((col r 1).drop stem.length).toString
      require ((col r 1).startsWith stem && digits suffix && suffix.length ≥ 4) (if table == "pages" then "page ID/source mismatch" else "claim ID/source mismatch")
      require (!(d.sourceRow (col r 2)).isEmpty) "unknown page or claim source"
      if table == "pages" then require (digits (col r 3) && (col r 3).length == 6) "bad page order key"
      else
        let page := d.row "pages" (col r 4)
        require (!page.isEmpty && col page 2 == col r 2) "claim source/page mismatch"
        require (orderKey (col r 3)) "bad claim order key"
        require (((col r 3).take 6).toString == col page 3) "claim/page order mismatch"
      let key := globalKey d (col r 2) (col r 3)
      require (previous.isEmpty || previous < key) "page or claim rows are not in global source order"
      previous := key
  dependencies d

/-- Capability and lifecycle ranks, with no source-stage inference from infrastructure. -/
def rank (s : String) : Nat :=
  ((#["registered","source_frozen","census_pass1","census_pass2","census_reconciled","vocabulary_reviewed","skeleton_frozen","proof_active","complete"].findIdx? (· == s)).map (· + 1)).getD 0
/-- Current checker capability from the exact one-row table. -/
def phase (d : Data) : String := (d.table "phase").records[1]?.getD ""
/-- Reviewed target coverage is distinct from excluded and historical records. -/
def vocabularyCoverage (d : Data) (allReviewed : Bool) : IO Unit := do
  let claims := (d.table "claims").rows; let reviews := (d.table "claim-vocabulary-review").rows
  let uses := (d.table "claim-vocabulary").rows
  let grouped := reviews.groupByKey (col · 1)
  let usedClaims := uses.foldl (fun m r => m.insert (col r 1)) ({} : Std.HashSet String)
  let usedVocabulary := uses.foldl (fun m r => m.insert (col r 2)) ({} : Std.HashSet String)
  for r in claims do
    let rs := grouped[col r 1]?.getD #[]
    let active := col r 12 == "false"; let target := active && col r 6 != "out_of_scope"
    let reviewed := allReviewed || rank (col (d.row "source-progress" (col r 2)) 2) ≥ 6
    if reviewed && target then require (rs.size == 1) s!"active claim lacks exactly one vocabulary review {col r 1}"
    require (target || rs.isEmpty) (if active then "out-of-scope claim has vocabulary review" else "tombstoned claim has vocabulary review")
    let used := usedClaims.contains (col r 1)
    let basis := col (rs[0]?.getD #[]) 2
    require (basis != "mathlib_only" || !used) "mathlib-only claim has project vocabulary"
    require (!reviewed || basis != "project_vocabulary" || used) "project-vocabulary claim lacks vocabulary use"
  for r in (d.table "vocabulary").rows do
    require (usedVocabulary.contains (col r 1)) s!"unused vocabulary declaration {col r 1}"
/-- Modern source lifecycle constraints and target vocabulary coverage. -/
def lifecycle (d : Data) : IO Unit := do
  present d #["phase","sources","source-invariants","source-progress","claims","claim-vocabulary-review","vocabulary","claim-vocabulary"]
  phaseRead d
  let cap := match phase d with
    | "bootstrap" => 2 | "census" => 5 | "vocabulary" => 6 | "skeleton" => 7 | "proof" => 9 | _ => 0
  let progress := (d.table "source-progress").rows
  for r in progress do
    let id := col r 1; let life := col r 2; let n := rank life
    let source := d.sourceRow id; let coverage := col source 17
    require (n > 0 && n ≤ cap) s!"source lifecycle exceeds checker capability {id}"
    if life == "registered" then require (coverage == "pending" && (col source 15).isEmpty && (col source 16).isEmpty) "registered source must be unfrozen and pending"
    if life == "source_frozen" then require (coverage == "pending" && oid (col source 15) && oid (col source 16)) "source_frozen requires OIDs and pending coverage"
    for (a,b) in #[("census_pass1","pass1"),("census_pass2","pass2"),("census_reconciled","reconciled")] do
      require (life != a || coverage == b) s!"{a} coverage mismatch"
    require (n < 6 || coverage == "frozen") "post-census lifecycle requires frozen coverage"
    require (n < 3 || (oid (col source 15) && oid (col source 16) && (col source 15).length == (col source 16).length)) "census lifecycle requires frozen source OIDs"
    require ((n ≥ 5) == d.has "source-invariants" id) "reconciled source invariant membership mismatch"
  require (d.sources.all fun r => has progress (col r 1)) "source lacks lifecycle"
  vocabularyCoverage d false

/-- Load existing table bytes once; schema owners decide which tables are mandatory. -/
def load (root : System.FilePath) (names : Array String := headers.map (·.1)) : IO Data := do
  let mut tables := #[]
  for (name, _) in headers do
    if !names.contains name then continue
    let path := root / "registry" / (name ++ ".tsv")
    if ← path.pathExists then tables := tables.push (name, tableFromText (← IO.FS.readFile path))
  if names.contains "reference" && (← (root / "references/tasaki-2020.tsv").pathExists) then
    tables := tables.push ("reference", tableFromText (← IO.FS.readFile (root / "references/tasaki-2020.tsv")))
  pure ⟨root, tables⟩
/-- Check requested headers and exact row shapes without silently dropping missing files. -/
def tables (d : Data) (names : Array String) : IO Unit := do
  for name in names do
    let header := ((headers.find? (·.1 == name)).map (·.2)).getD ""
    require (!header.isEmpty) "unknown table schema"
    schemaTable d name header
/-- Complete modern structural schema and checker capability. -/
def schema (d : Data) : IO Unit := do
  phaseRead d
  tables d (headers.map (·.1))
  require ((d.table "phase").records.size == 2 && oneOf (phase d) "bootstrap|census|vocabulary|skeleton|proof") "bad checker capability or phase row count"

/-- Legacy source reference retains its exact fixture-only schema and atomic freeze rules. -/
def reference (d : Data) : IO Unit := do
  schemaTable d "reference" "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes"
  require (d.sources.size == 1) "legacy fixture requires exactly one reference row"
  let r := d.sources[0]!
  require (col r 1 == "TASAKI2020" && !(col r 2).isEmpty && !(col r 3).isEmpty) "legacy fixture identity must be TASAKI2020"
  require (((col r 4).isEmpty == (col r 5).isEmpty) &&
    ((col r 4).isEmpty || (oid (col r 4) && oid (col r 5) && (col r 4).length == (col r 5).length))) "bad source OID pair"
  require (oneOf (col r 6) "pending|pass1|pass2|reconciled|frozen") "bad coverage"
  let edition := ((col r 3).toList.head?.map alnum).getD false && (col r 3).toList.all (fun c => alnum c || "._+-".contains c) &&
    !oneOf (col r 3).toLower "unspecified|pending|unknown|none"
  if phase d == "bootstrap" then
    require (col r 6 == "pending" &&
      ((col r 3 == "unspecified" && (col r 4).isEmpty && (col r 5).isEmpty) ||
       (edition && oid (col r 4) && oid (col r 5))))
      "bootstrap reference must be either unverified or atomically source-frozen, with pending coverage"
  else
    require (edition && !(col r 4).isEmpty && (col r 4).length == (col r 5).length && col r 6 != "pending")
      "post-bootstrap reference requires verified edition, equal-width OIDs, and non-pending coverage"
/-- Pure common page/claim, supersession and legacy-slice checks. -/
def claims (d : Data) : IO Unit := do
  let pages := (d.table "pages").rows; let cs := (d.table "claims").rows
  increasing pages 2 3 "page order is not strictly increasing"
  for r in pages do
    require (stableId (col r 1) "PG") "bad page ID"
    require (!(d.sourceRow (col r 2)).isEmpty) "unknown source"
    require (digits (col r 3) && (col r 3).length == 6) "bad page order key"
    require (!(col r 4).isEmpty && col r 4 != "unspecified") "missing printed page label must use NONE"
    require (digits (col r 5) true) "PDF page must be a positive integer"
    require (!(col r 6).isEmpty) "missing section must use NONE"
    require (oneOf (col r 7) "content|front_matter|back_matter|blank|index") "bad page kind"
    require (oneOf (col r 8) "pending|complete|disputed" && oneOf (col r 9) "pending|complete|disputed") "bad census pass value"
    require (col r 10 == "PENDING" || oid (col r 10)) "bad source OID"
    require (col r 8 != "complete" || col r 9 != "complete" || col r 10 != "PENDING") "two-pass-complete page needs a frozen source OID"
  increasing cs 2 3 "claim order is not strictly increasing"
  let mut edges := #[]
  for r in cs do
    require (stableId (col r 1) "CL") "bad claim ID"
    require (!(d.sourceRow (col r 2)).isEmpty && d.has "pages" (col r 4) && col (d.row "pages" (col r 4)) 2 == col r 2) "bad claim source/page foreign key"
    require (claimOrder (col r 3)) "bad claim order key"
    require (!(col r 5).isEmpty && !(col r 8).isEmpty) "empty locator or normalized content"
    require (oneOf (col r 6) "assertion|definition|notation|hypothesis|domain|conjecture|out_of_scope") "bad disposition"
    require (oneOf (col r 7) "theorem|lemma|proposition|corollary|equation|definition|notation|problem|remark|subclaim|unnumbered_obligation|hypothesis|domain|conjecture") "bad subkind"
    require (col r 9 == "PENDING" || oid (col r 9)) "bad content OID"
    if col r 6 == "out_of_scope" then
      require (token (col r 10) && col r 10 != "NONE" && token (col r 11) && col r 11 != "NONE") "out_of_scope needs exclusion rationale and review ref"
    else require (col r 10 == "NONE" && col r 11 == "NONE") "non-excluded claim must use NONE exclusion fields"
    require (oneOf (col r 12) "false|true") "bad tombstone flag"
    if col r 12 == "false" then
      require (#[13,14,15].all (col r · == "NONE")) "active claim has supersession metadata"
    else
      require (d.has "claims" (col r 13) && col r 13 != col r 1) "unknown or self superseded_by"
      require (token (col r 14) && col r 14 != "NONE" && token (col r 15) && col r 15 != "NONE") "tombstone needs successor, rationale, and review ref"
      edges := edges.push (col r 1,col r 13)
  acyclic edges "supersession cycle"
  if !d.multi then
    let slices := (d.table "slices").rows
    unique slices #[3] "claim occurs in multiple slice rows"
    unique slices #[1,3] "duplicate slice membership"
    contiguous slices 1 2 "non-contiguous slice position"
    for r in slices do
      require (stableId (col r 1) "SL" true && d.has "claims" (col r 3)) "bad slice ID or claim"
    if !slices.isEmpty then
      require (cs.all fun c => col c 12 != "false" || slices.any (col · 3 == col c 1)) "claim missing from slices"
    dependencies d
/-- Binding and context fields retain the distinction between proof and definitional contracts. -/
def bindings (d : Data) : IO Unit := do
  let cs := (d.table "claims").rows; let bs := (d.table "bindings").rows
  unique bs #[2] "duplicate statement declaration"
  unique (bs.filter (col · 9 == "proof_stub")) #[3] "duplicate proof declaration"
  for r in bs do
    let c := d.row "claims" (col r 1); let proof := col r 9 == "proof_stub"
    require (!c.isEmpty && col c 12 == "false") "unknown or inactive binding claim"
    require (col c 6 != "out_of_scope") "out-of-scope claim has a binding"
    require (name (col r 2) && name (col r 4)) "bad statement declaration or module"
    require (col (d.row "statement-modules" (col r 4)) 3 == "leaf") "binding needs a registered statement leaf module"
    require (oneOf (col r 5) "definition|abbrev") "bad statement kind"
    require (oneOf (col r 6) "proof_proposition|definition_value|definition_relation|notation_expansion|notation_relation|hypothesis_prop|domain_type|domain_predicate|domain_context") "bad statement shape"
    require ((#[7,8].all fun n => col r n == "PENDING" || oid (col r n))) "bad statement type or value OID"
    require (oneOf (col r 9) "proof_stub|definitional") "bad implementation status"
    if proof then
      require (name (col r 3) && col r 10 == "theorem" && (col r 11 == "PENDING" || oid (col r 11))) "proof stub metadata is incomplete"
      require (if phase d == "proof" then col r 12 == "NONE" || oid (col r 12) else col r 12 == "NONE") "R4/R5 proof value OID mismatch"
      require (col r 6 == "proof_proposition") "proof claim has non-proposition shape"
    else require (#[3,10,11,12].all (col r · == "NONE")) "definitional binding has proof metadata"
    require ((oneOf (col c 6) "assertion|conjecture") == proof) "implementation status/disposition mismatch"
    for (disp,shapes) in #[("definition","definition_value|definition_relation"),("notation","notation_expansion|notation_relation"),("hypothesis","hypothesis_prop"),("domain","domain_type|domain_predicate|domain_context")] do
      require (col c 6 != disp || oneOf (col r 6) shapes) s!"{disp} claim shape mismatch"
    require ((col r 13 == "NONE") == (col r 14 == "NONE")) "nonvacuity declaration/OID must be NONE together"
    require (col r 13 == "NONE" || name (col r 13)) "bad nonvacuity declaration"
    require (oneOf (col r 14) "NONE|PENDING" || oid (col r 14)) "bad nonvacuity OID"
    require (!(col r 15).isEmpty && col r 15 != "NONE") "binding needs review_ref"
  let contexts := (d.table "claim-context").rows
  if !contexts.isEmpty then
    require (d.tables.any (·.1 == "item-claims")) "claim-context rows require registry/item-claims.tsv"
  let contextItems := (d.table "item-claims").rows.foldl
    (fun m r => m.insert (col r 3) (col r 1)) ({} : Std.HashMap String String)
  contiguous contexts 1 2 "non-contiguous claim-context position"
  for r in contexts do
    let owner := d.row "claims" (col r 1); let setup := d.row "claims" (col r 3)
    require (!owner.isEmpty && !setup.isEmpty) "unknown claim-context claim"
    require (#[owner,setup].all fun c => col c 12 == "false" && col c 6 != "out_of_scope") "inactive claim-context owner or target"
    require (col r 1 != col r 3) "self claim-context"
    require ((cs.findIdx? (col · 1 == col r 3)).getD cs.size < (cs.findIdx? (col · 1 == col r 1)).getD 0) "claim-context target is not earlier"
    require (oneOf (col setup 6) "definition|notation|hypothesis|domain") "claim-context target is not a setup claim"
    require (oneOf (col r 4) "assumption|term_reference" && oneOf (col r 5) "same_item|inherited") "bad claim-context use kind or scope"
    if col r 5 == "same_item" then
      let a := contextItems[col r 1]?.getD ""
      let b := contextItems[col r 3]?.getD ""
      require (!a.isEmpty && a == b) "same_item claim-context crosses source items"
    require (!(col r 6).isEmpty && col r 6 != "NONE") "claim-context needs review_ref"
/-- Registered intentional axioms are category-owned and linked only by valid claim relations. -/
def axioms (d : Data) : IO Unit := do
  let ax := (d.table "axioms").rows
  for r in ax do
    require (stableId (col r 1) "AX" true) "bad axiom ID"
    require (#[2,3,5,6,7].all fun n => !(col r n).isEmpty) "empty axiom field"
    require (col r 8 == "PENDING" || oid (col r 8)) "bad axiom type OID"
    let categories := #[("abstract_cstar","AbstractCStar"),("state","State"),("gns","GNS"),("kms","KMS"),("weak_dual","WeakDual"),("wigner","Wigner"),("contentless_predicate","ContentlessPredicate")]
    let found := categories.find? (·.1 == col r 4)
    require found.isSome "bad axiom category"
    let expected := "LatticeSystem.Axioms." ++ found.get!.2
    require (col r 3 == expected && (col r 2).startsWith (expected ++ ".")) "axiom declaration/module does not match category namespace"
  for r in (d.table "claim-axioms").rows do
    require (d.has "claims" (col r 1) && has ax (col r 2)) "bad claim-axiom foreign key"
/-- Vocabulary identity, generated-parent and target-use structural constraints. -/
def vocabulary (d : Data) : IO Unit := do
  let vs := (d.table "vocabulary").rows
  unique vs #[2] "duplicate vocabulary declaration"
  let mut previous := ""
  for r in vs do
    let id := col r 1
    require ((id.startsWith "VO-LS-" && digits (id.drop 6).toString && (id.drop 6).toString.length ≥ 4) || oneOf id "VO-TASAKI2020-0001|VO-TASAKI2020-0002") "bad vocabulary ID"
    require (projectName (col r 2) && projectName (col r 3)) "vocabulary declaration and module must be below LatticeSystem"
    require (oneOf (col r 4) "definition|abbrev|inductive|structure|class|constructor|recursor|projection|instance") "bad vocabulary declaration kind"
    require (oneOf (col r 5) "primary|generated") "bad vocabulary origin"
    require (#[7,8].all fun n => col r n == "PENDING" || oid (col r n)) "bad vocabulary type or declaration OID"
    require (oneOf (col r 9) "graph_core|finite_volume|linear_algebra|operator_algebra|quantum_state|stat_mech|fermion|generated") "bad vocabulary design role"
    require (oneOf (col r 10) "none|local_operation|explicit_finite_volume|inherited") "bad vocabulary finiteness scope"
    if col r 5 == "primary" then
      require (col r 6 == "NONE" && col r 9 != "generated" && col r 10 != "inherited") "primary vocabulary cannot use generated metadata"
    else
      require (col r 6 != "NONE" && !(col r 6).isEmpty && col r 6 != id && col (d.row "vocabulary" (col r 6)) 5 == "primary") "unknown or non-primary vocabulary parent"
      require (oneOf (col r 4) "constructor|recursor|projection" && col r 9 == "generated" && col r 10 == "inherited") "generated vocabulary needs generated/inherited metadata"
    require (previous.isEmpty || previous < id) "vocabulary IDs are not strictly increasing"
    previous := id
    require (col (d.row "modules" (col r 3)) 3 == "leaf") "vocabulary declaration needs a registered leaf module"
  for r in (d.table "claim-vocabulary-review").rows do
    require (d.has "claims" (col r 1)) "unknown vocabulary-review claim"
    require (col (d.row "claims" (col r 1)) 12 == "false") "tombstoned claim has vocabulary review"
    require (oneOf (col r 2) "mathlib_only|project_vocabulary" && token (col r 3)) "bad vocabulary basis or review token"
  for r in (d.table "claim-vocabulary").rows do
    require (d.has "claims" (col r 1) && col (d.row "claims" (col r 1)) 12 == "false") "bad claim-vocabulary claim"
    require (d.has "vocabulary" (col r 2)) "unknown claim-vocabulary ID"
/-- Module identities, exact physical paths, import flags and graph cycles. -/
def modules (d : Data) : IO Unit := do
  let vocabularyModules := (d.table "modules").rows
  let statementModules := (d.table "statement-modules").rows
  for table in #["modules","statement-modules"] do
    let rows := (d.table table).rows
    unique rows #[2] "duplicate module source path"
    for r in rows do
      require (projectName (col r 1) true) "bad registered module"
      require (col r 2 == (col r 1).replace "." "/" ++ ".lean") "module/source path mismatch"
      require (oneOf (col r 3) (if table == "modules" then "leaf|umbrella|root" else "leaf|umbrella")) "bad module role"
      if table == "modules" then
        require ((col r 3 == "root") == (col r 1 == "LatticeSystem" && col r 2 == "LatticeSystem.lean")) "root module identity mismatch"
      else require (!has vocabularyModules (col r 1)) "module is registered in both vocabulary and statement registries"
    if !rows.isEmpty then
      require ((rows.filter (col · 3 == if table == "modules" then "root" else "umbrella")).size == 1)
        (if table == "modules" then "module registry needs exactly one root" else "statement module registry needs exactly one umbrella")
  for (table,owners) in #[("imports",vocabularyModules),("statement-imports",statementModules)] do
    let rows := (d.table table).rows
    contiguous rows 1 2 (if table == "imports" then "non-contiguous import position" else "non-contiguous statement import position")
    let project := if table == "imports" then vocabularyModules else vocabularyModules ++ statementModules
    let mut edges := #[]
    for r in rows do
      require (has owners (col r 1)) "import owner is not registered"
      require (name (col r 3)) "bad imported module"
      require (#[4,5,6].all fun n => oneOf (col r n) "false|true") "bad import flag"
      require (col r 1 != col r 3) "self import"
      if (col r 3).startsWith "LatticeSystem." then
        require (has project (col r 3)) "unregistered project import"
      else
        require (col r 3 == "LatticeSystem" || col r 3 == "Mathlib" || (col r 3).startsWith "Mathlib.")
          (if table == "imports" then "unauthorized external import" else "unauthorized statement external import")
      if has owners (col r 3) then edges := edges.push (col r 1,col r 3)
    acyclic edges (if table == "imports" then "project import cycle" else "statement import cycle")
/-- Native common registry validation, excluding already-composed modern prerequisite gates. -/
def registryCore (d : Data) : IO Unit := do
  phaseRead d
  tables d #["phase","pages","claims","slices","dependencies","bindings","claim-context","axioms","claim-axioms","claim-vocabulary-review","vocabulary","claim-vocabulary","modules","imports","statement-modules","statement-imports"]
  require ((d.table "phase").records.size == 2 && oneOf (phase d) "bootstrap|census|vocabulary|skeleton|proof") "bad phase or phase row count"
  if !d.multi then reference d
  for table in #["pages","claims","bindings","axioms","claim-vocabulary-review","vocabulary","modules","statement-modules"] do
    unique (d.table table).rows #[1] s!"{table}: duplicate first-column ID"
  unique d.sources #[1] "duplicate first-column source ID"
  for (table,columns) in #[("claim-axioms",#[1,2]),("claim-vocabulary",#[1,2]),("imports",#[1,2]),("statement-imports",#[1,2]),("claim-context",#[1,2])] do
    unique (d.table table).rows columns s!"{table}: duplicate composite key"
  let stages := #["pages","claims","slices","dependencies","bindings","claim-context","axioms","claim-axioms","claim-vocabulary-review","vocabulary","claim-vocabulary","modules","imports","statement-modules","statement-imports"]
  if phase d == "bootstrap" then emptyTables d stages "bootstrap requires"
  claims d; bindings d; axioms d; vocabulary d; modules d
  if phase d == "vocabulary" then
    emptyTables d #["slices","dependencies","bindings","claim-context","axioms","claim-axioms","statement-modules","statement-imports"] "vocabulary requires"
    if !d.multi then vocabularyCoverage d true
    require ((d.table "vocabulary").rows.all fun r => col r 7 != "PENDING" && col r 8 != "PENDING") "vocabulary capability forbids pending declaration OIDs"
  if oneOf (phase d) "skeleton|proof" then
    require ((d.table "bindings").rows.all fun r => #[7,8,11,14].all (col r · != "PENDING")) s!"{phase d} capability forbids pending binding OIDs"
    require ((d.table "axioms").rows.all (col · 8 != "PENDING")) s!"{phase d} capability forbids pending axiom OIDs"
/-- Source-item identities and one-to-one claim membership include historical records. -/
def items (d : Data) : IO Unit := do
  present d #["tracks","sources","pages","claims","source-items","item-claims"]
  let rows := (d.table "source-items").rows; let cs := (d.table "claims").rows
  let relations := (d.table "item-claims").rows
  unique rows #[1] "duplicate item ID"
  let mut previous := ""
  for r in rows do
    let stem := "IT-" ++ col r 2 ++ "-"; let suffix := ((col r 1).drop stem.length).toString
    require ((col r 1).startsWith stem && digits suffix && suffix.length ≥ 4) "item ID/source mismatch"
    require (!(d.sourceRow (col r 2)).isEmpty) "unknown item source"
    require (d.has "pages" (col r 4) && col (d.row "pages" (col r 4)) 2 == col r 2) "item source/page mismatch"
    require (orderKey (col r 3)) "bad item order key"
    require (((col r 3).take 6).toString == col (d.row "pages" (col r 4)) 3) "item/page order mismatch"
    require (oneOf (col r 5) "theorem|lemma|corollary|proposition|definition|problem|conjecture|example|exercise|remark|note|equation|figure|footnote|table|unlabeled") "bad item kind"
    require ((col r 5 == "unlabeled") == (col r 6 == "NONE")) "item label/kind mismatch"
    require (col r 6 == "NONE" || (col r 6).isEmpty || ((col r 8).splitOn (col r 6)).length > 1) "item locator does not contain exact label"
    require (!(col r 7).isEmpty && !(col r 8).isEmpty) "empty item title or locator"
    if (col r 9).startsWith "Chapter " && digits ((col r 9).drop 8).toString then
      require (col r 9 == "Chapter " ++ pad 2 (toString (((col r 9).drop 8).toString.toNat!))) "numeric chapter group is not zero-padded"
    require (!(col r 9).isEmpty && col r 10 == slugify (col r 9)) "item public group/slug mismatch"
    require (token (col r 11)) "bad item review token"
    let key := globalKey d (col r 2) (col r 3)
    require (previous.isEmpty || previous < key) "items are not in global source order"
    previous := key
  unique relations #[1,3] "duplicate item/claim relation"
  unique relations #[3] "claim occurs in more than one item"
  contiguous relations 1 2 "item relation positions are not contiguous"
  for r in relations do
    let item := d.row "source-items" (col r 1); let claim := d.row "claims" (col r 3)
    require (!item.isEmpty && !claim.isEmpty) "unknown item or claim relation"
    require (col item 2 == col claim 2 && col item 4 == col claim 4) "item/claim source or page mismatch"
    require (col r 2 != "1" || col item 3 == col claim 3) "item order does not match first claim"
  let usedItems := relations.foldl (fun m r => m.insert (col r 1)) ({} : Std.HashSet String)
  let usedClaims := relations.foldl (fun m r => m.insert (col r 3)) ({} : Std.HashSet String)
  require (rows.all fun r => usedItems.contains (col r 1)) "item has no claims"
  require (cs.all fun r => usedClaims.contains (col r 1)) "claim lacks exactly one source item"

/-- The exact locator suffix used for one equation occurrence. -/
def equationLabel (locator : String) : Option String := do
  let parts := split locator "; equation "
  if parts.size < 2 then none else
    let label := parts.back!
    if label.startsWith "(" && label.endsWith ")" && label.length > 2 &&
      !((label.drop 1).toString.dropEnd 1).toString.toList.any (fun c => c == '(' || c == ')')
    then some label else none
/-- A completed page census has exact contiguous physical identities and two frozen passes. -/
def censusPages (rows : Array Row) (source : String) (expected : Nat) (diagnostic : String) : IO Unit := do
  require (rows.size == expected) diagnostic
  for i in [:rows.size] do
    let r := rows[i]!; let n := toString (i + 1)
    require (col r 1 == "PG-" ++ source ++ "-" ++ pad 4 n && col r 2 == source && col r 3 == pad 6 n && col r 5 == n &&
      !(col r 4).isEmpty && col r 4 != "unspecified" && !(col r 6).isEmpty && !(col r 7).isEmpty &&
      col r 8 == "complete" && col r 9 == "complete" && oid (col r 10)) diagnostic
/-- Counts, active qualifications and equation occurrence pairs are distinct census obligations. -/
def censusClaims (pages cs : Array Row) (source : String) (expected targets equations empty : Nat)
    (modern : Bool) (diagnostic : String) : IO Unit := do
  let mut used : Std.HashSet String := {}; let mut pairs : Std.HashSet (String × String) := {}
  let mut equationCount := 0
  require (cs.size == expected && (modern || !cs.isEmpty)) diagnostic
  if modern then require ((cs.filter (col · 6 != "out_of_scope")).size == targets) diagnostic
  let pageMap := pages.foldl (fun m r => m.insert (col r 1) (col r 3)) ({} : Std.HashMap String String)
  let mut previous := ""
  for r in cs do
    require (!(col r 4).isEmpty && !(col r 5).isEmpty && !(col r 8).isEmpty &&
      (#[13,14,15].all (col r · == "NONE"))) diagnostic
    used := used.insert (col r 4)
    if !modern then
      require (col r 2 == source && (split (col r 3) ".").size == 2 && orderKey (col r 3) &&
        pageMap.contains (col r 4) && ((col r 3).take 6).toString == pageMap[col r 4]! &&
        col r 12 == "false" && (previous.isEmpty || previous < col r 3)) diagnostic
      previous := col r 3
    if col r 7 == "equation" then
      let some label := equationLabel (col r 5) | throw <| IO.userError diagnostic
      let pair := (col r 4,label)
      require (!pairs.contains pair) diagnostic
      pairs := pairs.insert pair
      equationCount := equationCount + 1
  require (equationCount == equations) diagnostic
  if modern then require ((pages.filter fun p => !used.contains (col p 1)).size == empty) diagnostic
/-- Source census arithmetic and exact printed-row LF hashing; prerequisite gates are composed by callers. -/
def census (d : Data) (fixture : Bool) (counts : Array Nat) : IO Unit := do
  phaseRead d
  if phase d == "bootstrap" then
    require (!fixture) "census fixture must use a post-bootstrap capability"
    IO.println "check-census: bootstrap capability; census completion gate not active"
    return
  require (oneOf (phase d) "census|vocabulary|skeleton|proof") "unknown post-bootstrap checker capability"
  let ps := (d.table "pages").rows; let cs := (d.table "claims").rows
  if d.multi then
    for progress in (d.table "source-progress").rows do
      if rank (col progress 2) < 5 then continue
      let source := col progress 1; let invariant := d.row "source-invariants" source
      require (!invariant.isEmpty) s!"reconciled source lacks invariants: {source}"
      let pages := ps.filter (col · 2 == source)
      censusPages pages source (col invariant 2).toNat!
        s!"page census invariant failed for {source}; page census is not exact, contiguous, two-pass complete, and source-frozen"
      censusClaims pages (cs.filter fun r => col r 2 == source && col r 12 == "false") source
        (col invariant 3).toNat! (col invariant 4).toNat! (col invariant 5).toNat! (col invariant 6).toNat! true
        s!"claim census invariant failed for {source}; claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
      let mut text := ""
      for table in #["pages","claims"] do
        for record in (d.table table).records.toList.drop 1 do
          if col (split record "\t") 2 == source then text := text ++ record ++ "\n"
      let actual := trim (← output d.root "git" #["hash-object","--stdin"] (some text))
      require (actual == col invariant 7) s!"census OID mismatch for {source}"
  else
    let ref := d.table "reference"; let r := ref.rows[0]?.getD #[]
    let sourceDiagnostic := if fixture then "fixture source is not verified and frozen" else
      "production source identity, fingerprints, or coverage are not frozen exactly"
    require (ref.records.size == 2 && ref.records[0]! == "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes" &&
      r.size == 7 && col r 1 == "TASAKI2020" && oid (col r 4) && oid (col r 5) &&
      (col r 4).length == (col r 5).length && col r 6 == "frozen" &&
      !oneOf (col r 3).toLower "unspecified|pending|unknown|none") sourceDiagnostic
    if !fixture then
      require (col r 2 == "Hal.Tasaki.P534.Physics_and_Mathematics_of_Quantum_Many_Body_Systems.pdf" &&
        col r 3 == "2020.springer.ebook.9783030412654" && col r 4 == "91d1237a6384d470bcdc453f058f8e08603767c5" &&
        col r 5 == "342ef0ce220dd3ed1c6cc0cdfab5a4d86bbd044f") sourceDiagnostic
    censusPages ps "TASAKI2020" counts[0]! "page census is not exact, contiguous, two-pass complete, and source-frozen"
    censusClaims ps cs "TASAKI2020" counts[1]! 0 counts[2]! 0 false
      "claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  if phase d == "census" then
    emptyTables d #["slices","dependencies","bindings","claim-context","axioms","claim-axioms","statement-modules","statement-imports"]
      (if d.multi then "census capability requires" else "census requires")
/-- C-locale lexical token boundaries are defense in depth, separate from semantic Lean checks. -/
def words (text : String) : Array String :=
  (split (text.map fun c => if c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13) then ' ' else c) " ").filter (!·.isEmpty)
/-- Production root isolation, phase-aware lexical hygiene and the exact user-only merge predicates. -/
def policy (d : Data) : IO Unit := do
  phaseRead d
  let source := d.root / "LatticeSystem.lean"
  require (← source.pathExists) "missing LatticeSystem.lean"
  let actual := trim (← git d.root #["hash-object",source.toString])
  let canonical := "f94581f054ad1f1a0b343257b72d1e81c2d786c9"
  let vocabularyRoot := "3936875b61b943e3a28c70410b049d6be2d431c5"
  let staging := phase d == "census" && !(d.table "modules").rows.isEmpty
  match phase d with
  | "bootstrap" =>
    require (actual == canonical) "declaration-free production root differs from canonical doc-only content"
    require (!(← (d.root / "LatticeSystem").isDir)) "bootstrap phase must not contain a production source directory"
  | "census" =>
    require (actual == if staging then vocabularyRoot else canonical) "census production root differs from canonical content"
    if !staging then require (!(← (d.root / "LatticeSystem").isDir)) "declaration-free census must not contain a production source directory"
  | "vocabulary" => require (actual == vocabularyRoot) "vocabulary root differs from canonical registered umbrella import"
  | "skeleton" =>
    require (actual == vocabularyRoot) "skeleton root differs from canonical registered umbrella import"
    require (!(d.table "statement-modules").rows.isEmpty) "skeleton phase requires registered statement modules"
  | "proof" => throw <| IO.userError "production policy is not implemented for proof"
  | _ => throw <| IO.userError "unknown phase"
  if oneOf (phase d) "vocabulary|skeleton" || staging then
    let tracked ← git d.root #["ls-files","-z","LatticeSystem.lean","LatticeSystem/*.lean","LatticeSystem/**/*.lean"]
    for path in (split tracked "\u0000").filter (!·.isEmpty) do
      let statement := (d.table "statement-modules").rows.any (col · 2 == path)
      let vocab := (d.table "modules").rows.any (col · 2 == path)
      require (!statement || !vocab) s!"source path is registered as both a vocabulary and a statement module: {path}"
      let tokens := if statement then #["admit","native_decide"] else #["axiom","theorem","lemma","sorry","admit","native_decide"]
      require (!(words (← IO.FS.readFile (d.root / path))).any tokens.contains)
        s!"vocabulary lexical hygiene found a forbidden token (nonsemantic check): {path}"
  for path in #["README.md","DESIGN.md",".github/pull_request_template.md"] do
    let text ← IO.FS.readFile (d.root / path)
    require ((text.splitOn "exact PR").length > 1) s!"{path} omits exact PR merge gate"
    require ((text.splitOn "exact head SHA").length > 1) s!"{path} omits exact head SHA merge gate"
    if path == ".github/pull_request_template.md" then
      require ((text.splitOn "- [x] USER ONLY").length == 1 && (text.splitOn "- [X] USER ONLY").length == 1) "USER ONLY gate is checked"
      require ((text.splitOn "- [ ] USER ONLY").length > 1) "template lacks unchecked USER ONLY gate"

end Registry


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
/-- Canonical input projections keep corpus bodies out of synthetic fixture signatures. -/
def payloads (root : System.FilePath) (rows : Array Entry)
    (headers registry policy history environment : Json) : IO (Json × String) := do
  let executable ← engine root rows
  let common := Json.mkObj [("engine", toJson executable), ("environment", environment),
    ("paths", Json.mkObj (rows.toList.map fun e => (e.path, toJson #[e.mode, e.kind]))),
    ("headers", headers), ("policy", policy)]
  let synthetic ← digest root common
  let corpus ← digest root <| common.mergeObj <| Json.mkObj [("registry", registry), ("historical", history)]
  pure (Json.mkObj <| suites.toList.map fun (name, _) =>
    (name, toJson (if #["checkers", "corrections", "content"].contains name then corpus else synthetic)), executable)

/-- Compute the two conservative actual-input signatures and independent engine hash. -/
def signatures (root : System.FilePath) (ref : String) (env : Json) : IO (Json × String) := do
  let rows ← entries root ref
  let mut headers := []; let mut registry := []; let mut policy := []
  for e in rows do
    require (e.kind == "blob") "non-blob tracked input"
    if e.path.startsWith "registry/" then
      let text ← git root #["show", ref ++ ":" ++ e.path]
      headers := (e.path, toJson (split text "\n")[0]!) :: headers
      registry := (e.path, toJson e.oid) :: registry
    if policyPaths.contains e.path then
      policy := (e.path, policyProjection e.path (← git root #["show", ref ++ ":" ++ e.path])) :: policy
  payloads root rows (Json.mkObj headers) (Json.mkObj registry) (Json.mkObj policy) (← historical root ref) env
/-- Decide whether an ordinary content change belongs to the narrow light surface. -/
def changeForcesFull (path status oldMode newMode : String) (headerChanged : Bool) : Bool :=
  if status != "M" || oldMode != newMode || !#["100644", "100755"].contains newMode then true
  else if path.startsWith "registry/" && path.endsWith ".tsv" then
    let name := ((path.drop 9).toString.dropEnd 4).toString
    semanticTables.contains name || !corpusTables.contains name || headerChanged
  else !#["README.md", "DESIGN.md"].contains path && !path.startsWith "docs/"
/-- Classify every raw-z endpoint; invalid Git operations fail rather than become an empty diff. -/
def fullRequired (root : System.FilePath) (base head : String) : IO Bool := do
  let raw := split (← git root #["diff", "--raw", "--no-renames", "--no-abbrev", "-z", base, head]) "\u0000"
  let mut full : Bool := raw.size ≤ 1
  for i in [:raw.size / 2] do
    let fields := split raw[i*2]! " "
    require (fields.size == 5) "invalid raw Git difference"
    let path := raw[i*2+1]!
    let mut headerChanged := false
    if fields[4]! == "M" && path.startsWith "registry/" && path.endsWith ".tsv" then
      let a ← git root #["show", base ++ ":" ++ path]
      let b ← git root #["show", head ++ ":" ++ path]
      headerChanged := (split a "\n")[0]! != (split b "\n")[0]!
    full := full || changeForcesFull path fields[4]! (fields[0]!.drop 1).toString fields[1]! headerChanged
  pure full

/-- Require an environment value, without putting secret values in diagnostics. -/
def env (key : String) : IO String := do
  let some value ← IO.getEnv key | throw <| IO.userError s!"missing environment key: {key}"
  require (!value.isEmpty) s!"empty environment key: {key}"
  pure value
/-- The pinned toolchain supplies its own compiler; caller PATH substitutions do not choose the native backend. -/
def toolchainRoot (root : System.FilePath) : IO System.FilePath := do
  IO.FS.realPath (trim (← output root "lean" #["--print-prefix"]))
/-- Hash an existing tool without logging its local installation path. -/
def toolDigest (root path : System.FilePath) : IO String := do
  let result ← output root "shasum" #["-a","256",path.toString]
  let hash := (split (trim result) " ")[0]!
  require (hex hash 64) "compiler identity unavailable"
  pure hash
/-- Bind runner image and installed tool versions for reuse, not local paths or secrets. -/
def environment (root : System.FilePath) : IO Json := do
  let mut fields := []
  for key in #["RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion"] do
    fields := (key, toJson (← env key)) :: fields
  for (name, command) in #[("lean", "lean"), ("lake", "lake"), ("git", "git"), ("bash", "bash"), ("python", "python3"), ("curl", "curl")] do
    let text ← output root command #["--version"]
    fields := (name, toJson (split text "\n")[0]!) :: fields
  let sysroot ← toolchainRoot root
  let nativeVersion ← output root (sysroot / "bin/leanc").toString #["--no-default-config","--version"]
  fields := ("native_compiler", Json.mkObj [
    ("driver",toJson (← toolDigest root (sysroot / "bin/leanc"))),
    ("backend",toJson (← toolDigest root (sysroot / "bin/clang"))),
    ("version",toJson ((split nativeVersion "\n").extract 0 2)),
    ("driver_path",toJson "bin/leanc"), ("backend_path",toJson "bin/clang")]) :: fields
  pure <| Json.mkObj fields
/-- A push binds payload before/after to the actual single-parent checkout, never origin/HEAD. -/
def pushBound (head base source : String) (actualParents : Array String) : Bool :=
  source == head && hex base 40 && base != String.ofList (List.replicate 40 '0') && actualParents == #[base]
/-- PR acceptance requires the exact synthetic base/source parents in order. -/
def syntheticBound (head base source : String) (actualParents : Array String) : Bool :=
  head != source && actualParents == #[base, source]
/-- Event-bound checkout identity; a production push never compares against its own trunk ref. -/
def context (root : System.FilePath) : IO Json := do
  require ((trim (← git root #["status", "--porcelain"])).isEmpty) "CI checkout must be clean"
  let event ← env "GITHUB_EVENT_NAME"
  let payload ← parse (← IO.FS.readFile (← env "GITHUB_EVENT_PATH"))
  let head ← commit root "HEAD"
  let (base, source) ← if event == "push" then do
    let base ← str payload "before"; let source ← str payload "after"
    require (pushBound head base source (← parents root head)) "push identity mismatch"
    pure (base, source)
  else if event == "pull_request" then do
    let pr ← field payload "pull_request"
    let baseRecord ← field pr "base"; let sourceRecord ← field pr "head"
    let base ← str baseRecord "sha"; let source ← str sourceRecord "sha"
    require ((← str baseRecord "ref") == "rewrite-main" && syntheticBound head base source (← parents root head)) "PR synthetic checkout mismatch"
    require (trim (← git root #["merge-base", base, source]) == base) "PR base is not up to date"
    pure (base, source)
  else throw <| IO.userError "unsupported CI event"
  let _ ← commit root base
  pure <| Json.mkObj [("event", toJson event), ("head", toJson head),
    ("source_head", toJson source), ("base", toJson base), ("tree", toJson (← tree root head))]
/-- Successful loaded evidence, including the actual executed job identity. -/
structure Loaded where
  /-- Parsed receipt after strict independent checks. -/
  receipt : Json
  /-- Producing run, attempt and job. -/
  origin : Json
/-- Bounded repository-only API access; token is never an argument or log value. -/
structure Evidence where
  /-- Exact repository scope. -/
  repository : String
  /-- Ephemeral token held only in memory/stdin. -/
  token : String
  /-- Monotonic deadline for the entire lookup. -/
  deadline : Nat
  /-- Independently expected executable identity. -/
  executable : String
  /-- Avoid repeating original-producer lookups within one verification. -/
  cache : IO.Ref (Array (Nat × Loaded))
/-- Explicit transport flags ignore user curl configuration and never forward cross-host credentials. -/
def curlArguments (repository suffix : String) (timeout : String := "8") : Array String := #["--disable", "--silent", "--show-error", "--fail", "--location",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "5", "--max-time", timeout,
  "--max-filesize", "8000000", "--config", "-", "https://api.github.com/repos/" ++ repository ++ suffix]
/-- Use curl's protected redirect semantics; never use location-trusted. -/
def http (root : System.FilePath) (e : Evidence) (suffix : String) : IO String := do
  let now ← IO.monoMsNow
  require (now < e.deadline) "evidence lookup budget exhausted"
  require (!(e.token.contains '\n') && !(e.token.contains '\r') &&
    !(e.token.contains '"') && !(e.token.contains '\\')) "invalid token encoding"
  let config := s!"header = \"Authorization: Bearer {e.token}\"\nheader = \"Accept: application/vnd.github+json\"\nheader = \"X-GitHub-Api-Version: 2022-11-28\"\n"
  let remaining := min 8000 (e.deadline - now)
  let fraction := (("00" ++ toString (remaining % 1000)).takeEnd 3).toString
  let timeout := s!"{remaining / 1000}.{fraction}"
  let result ← output root "curl" (curlArguments e.repository suffix timeout)
    (some config)
  require (result.utf8ByteSize ≤ 8000000) "oversized evidence"
  pure result
/-- Fetch only a JSON API response in the fixed repository. -/
def api (root : System.FilePath) (e : Evidence) (suffix : String) : IO Json := do parse (← http root e suffix)
/-- Validate the receipt format before considering any cache result. -/
def validReceipt (j : Json) : IO Unit := do
  require (exactKeys j #["version", "run_id", "run_attempt", "head", "source_head", "base", "tree",
    "event", "engine", "environment", "suites", "current", "transition", "build"]) "receipt fields mismatch"
  require ((← nat j "version") == version) "receipt version mismatch"
  for key in #["head", "source_head", "base", "tree"] do require (hex (← str j key) 40) "invalid receipt commit"
  for key in #["current", "transition", "build"] do require ((← str j key) == "success") "fresh gate not successful"
  let results ← field j "suites"
  require (exactKeys results (suites.map Prod.fst)) "suite set mismatch"
  for (name, _) in suites do
    let result ← field results name
    require (exactKeys result #["input", "result", "origin"] && hex (← str result "input") 64) "invalid suite receipt"
    let state ← str result "result"; let origin ← field result "origin"
    if state == "executed" then require origin.isNull "executed suite has foreign origin"
    else
      require (state == "reused" && exactKeys origin #["run_id", "run_attempt", "job_id"]) "invalid suite origin"
      for key in #["run_id", "run_attempt", "job_id"] do require ((← nat origin key) > 0) "invalid origin identity"
/-- Decode exactly one final versioned marker; duplicate or malformed logs are not evidence. -/
def receiptFromLog (log : String) : IO Json := do
  let hits := (split log "\n").filter fun line => (line.splitOn marker).length > 1
  require (hits.size == 1) "receipt marker missing or ambiguous"
  let pieces := split hits[0]! marker
  require (pieces.size == 2) "ambiguous receipt marker"
  let receipt ← parse pieces[1]!
  validReceipt receipt
  pure receipt
/-- Require a successful producer in the exact repository, workflow and event scope. -/
def validateRun (run : Json) (repository : String) (runId : Nat) : IO Nat := do
  require (runId > 0 && (← nat run "id") == runId && (← str run "status") == "completed" &&
    (← str run "conclusion") == "success" && (← str run "name") == "rewrite-ci" &&
    (← str run "path") == ".github/workflows/rewrite-ci.yml" &&
    (← str (← field run "repository") "full_name") == repository) "untrusted producing run"
  let event ← str run "event"
  require (event == "push" || event == "pull_request") "invalid producing event"
  if event == "push" then require ((← str run "head_branch") == "rewrite-main") "nonproduction push evidence"
  let attempt ← nat run "run_attempt"
  require (attempt > 0) "invalid attempt"
  pure attempt
/-- Require the exact successful job, not a skipped or previous-attempt result. -/
def validateJob (job : Json) (runId attempt : Nat) : IO Nat := do
  require ((← str job "name") == "verify" && (← str job "status") == "completed" &&
    (← str job "conclusion") == "success" && (← nat job "run_id") == runId &&
    (← nat job "run_attempt") == attempt) "unsuccessful verification job"
  let id ← nat job "id"
  require (id > 0) "invalid job identity"
  pure id
/-- Bind decoded receipt data to the successful server-side producer. -/
def validateIdentity (receipt run : Json) (runId attempt : Nat) (executable : String) : IO Unit := do
  require ((← nat receipt "run_id") == runId && (← nat receipt "run_attempt") == attempt &&
    (← str receipt "source_head") == (← str run "head_sha") &&
    (← str receipt "event") == (← str run "event") &&
    (← str receipt "engine") == executable) "receipt identity mismatch"
/-- Check actual parents/tree; a direct PR head is not a synthetic-checkout receipt. -/
def validateCheckout (receipt : Json) (actualParents : Array String) (actualTree : String) : IO Unit := do
  require (actualTree == (← str receipt "tree")) "checkout tree mismatch"
  let base ← str receipt "base"; let source ← str receipt "source_head"; let head ← str receipt "head"
  require (if (← str receipt "event") == "push" then pushBound head base source actualParents
    else syntheticBound head base source actualParents) "producing checkout ancestry mismatch"

/-- Load a single successful actual run/attempt/job and independently verify its executable tree. -/
def load (root : System.FilePath) (e : Evidence) (runId : Nat) : IO Loaded := do
  for (id, value) in ← e.cache.get do if id == runId then return value
  let run ← api root e s!"/actions/runs/{runId}"
  let attempt ← validateRun run e.repository runId
  let jobs ← api root e s!"/actions/runs/{runId}/attempts/{attempt}/jobs?per_page=100"
  let records ← arr jobs "jobs"
  require ((← nat jobs "total_count") == 1 && records.size == 1) "ambiguous verification job"
  let job := records[0]!
  let jobId ← validateJob job runId attempt
  let log ← http root e s!"/actions/jobs/{jobId}/logs"
  let receipt ← receiptFromLog log
  validateIdentity receipt run runId attempt e.executable
  let checkout ← api root e ("/git/commits/" ++ (← str receipt "head"))
  let actualParents ← (← arr checkout "parents").mapM fun parent => str parent "sha"
  validateCheckout receipt actualParents (← str (← field checkout "tree") "sha")
  let remote ← api root e ("/git/trees/" ++ (← str receipt "tree") ++ "?recursive=1")
  require ((← field remote "truncated") == Json.bool false) "truncated executable tree"
  let mut rows := #[]
  for row in ← arr remote "tree" do
    let kind ← str row "type"
    if kind != "tree" then rows := rows.push ⟨← str row "path", ← str row "mode", kind, ← str row "sha"⟩
  require ((← engine root rows) == e.executable) "producer executable bytes mismatch"
  let origin := Json.mkObj [("run_id", toJson runId), ("run_attempt", toJson attempt), ("job_id", toJson jobId)]
  let value := Loaded.mk receipt origin
  e.cache.modify (·.push (runId, value))
  pure value
/-- Bind each API candidate explicitly to the independently identified source head. -/
def candidates (root : System.FilePath) (e : Evidence) (ctx : Json) : IO (Array (Nat × String)) := do
  let event ← str ctx "event"
  let source ← if event == "pull_request" then str ctx "base" else do
    let pulls ← api root e ("/commits/" ++ (← str ctx "head") ++ "/pulls?per_page=10")
    let mut hits := #[]
    for pr in ← IO.ofExcept pulls.getArr? do
      let base ← field pr "base"; let head ← field pr "head"; let repo ← field head "repo"
      if !(← field pr "merged_at").isNull && (← str pr "merge_commit_sha") == (← str ctx "head") &&
        (← str base "ref") == "rewrite-main" && !repo.isNull && (← str repo "full_name") == e.repository then
        hits := hits.push (← str head "sha")
    require (hits.size == 1) "no unique merged PR evidence"
    pure hits[0]!
  require (hex source 40) "invalid candidate source"
  let kind := if event == "pull_request" then "push" else "pull_request"
  let result ← api root e s!"/actions/workflows/rewrite-ci.yml/runs?event={kind}&head_sha={source}&per_page=5"
  let mut found := #[]
  for run in ← arr result "workflow_runs" do
    if (← str run "status") == "completed" && (← str run "conclusion") == "success" then
      found := found.push ((← nat run "id"), source)
  pure <| found.extract 0 5
/-- PR engine changes require execution; an exact newly-tested postmerge tree may reuse. -/
def lookupAllowed (full : Bool) (event : String) : Bool := !full || event == "push"
/-- Every candidate is bound to its independently identified source, environment and checkout role. -/
def candidateBound (receipt ctx : Json) (source : String) (environment : Json) : IO Bool := do
  if (← field receipt "environment") != environment || (← str receipt "source_head") != source then return false
  if (← str ctx "event") == "pull_request" then
    return (← str receipt "head") == (← str ctx "base") && (← str receipt "event") == "push"
  return (← str receipt "event") == "pull_request" && (← str receipt "base") == (← str ctx "base") &&
    (← str receipt "tree") == (← str ctx "tree")
/-- Only an exact directly executed origin is reusable; no recursive receipt chain is accepted. -/
def originalBound (original : Loaded) (expected : Json) (name signature : String) (environment : Json) : IO Bool := do
  if original.origin != expected || (← field original.receipt "environment") != environment then return false
  return (← field (← field original.receipt "suites") name) == Json.mkObj [
    ("input", toJson signature), ("result", toJson "executed"), ("origin", Json.null)]
/-- Explicit full mode never reuses regressions; current mode never claims to have run them. -/
def regressionRequired (mode : String) (accepted : Json) (name : String) : Bool :=
  mode != "--current" && (mode == "--full" || (accepted.getObjValD name).isNull)

/-- Reuse only direct original executed results; malformed or unavailable evidence executes instead. -/
def reuse (root : System.FilePath) (e : Evidence) (ctx sigs environment : Json) : IO Json := do
  let mut accepted := Json.mkObj []
  for (id, source) in ← candidates root e ctx do
    try
      let candidate ← load root e id
      let j := candidate.receipt
      if !(← candidateBound j ctx source environment) then continue
      for (name, _) in suites do
        let result ← field (← field j "suites") name
        let signature ← str sigs name
        if (← str result "input") != signature then continue
        let mut origin := candidate.origin
        if (← str result "result") == "reused" then
          let expected ← field result "origin"
          let original ← load root e (← nat expected "run_id")
          if !(← originalBound original expected name signature environment) then continue
          origin := original.origin
        accepted := accepted.setObjVal! name origin
      if (keys accepted).size == suites.size then break
    catch _ => pure ()
  pure accepted

/-- One external gate with inherited output and a mandatory successful exit. -/
structure Command where
  /-- Existing program. -/
  cmd : String
  /-- Arguments never contain the API credential. -/
  args : Array String := #[]
  deriving Inhabited
/-- The sole current-data gate plan shared by every mode. -/
def currentPlan (root : System.FilePath) (phase : String) (moduleRows : Nat) : Array Command := Id.run do
  let mut plan := #[ ]
  if phase == "vocabulary" || moduleRows > 1 then plan := plan.push ⟨"scripts/check-vocabulary.sh", #[root.toString]⟩
  plan := plan.push ⟨"scripts/check-skeleton.sh", #[root.toString]⟩
  for mode in #["--test", "--check"] do
    plan := plan.push ⟨"python3", #["scripts/generate-public-docs.py", mode, "--root", root.toString]⟩
  return plan
/-- The shared sequential interpreter makes every current/selected failure fatal. -/
def execute (perform : Command → IO Unit) (plan : Array Command) : IO Unit :=
  plan.forM perform
/-- Run an ordinary verification command; unlike HTTP, no sensitive input is involved. -/
def runGate (root : System.FilePath) (command : Command)
    (childEnvironment : Array (String × Option String) := #[]) : IO Unit := do
  IO.println s!"check-all: run {command.cmd} {String.intercalate " " command.args.toList}"
  let child ← IO.Process.spawn {
    cmd := command.cmd, args := command.args, cwd := some root,
    stdin := .inherit, stdout := .inherit, stderr := .inherit, env := childEnvironment }
  require ((← child.wait) == 0) s!"verification failed: {command.cmd}"
/-- The nine current data/policy gates are native Lean functions, not shell programs. -/
def dataGates : Array String := #["tree","schema","sources","order","lifecycle","registry","census","source-items","policy"]
/-- Invoke one native validation core; prerequisite composition belongs to the owning entry route. -/
def dataCore (project : System.FilePath) (d : Registry.Data) (gate : String)
    (fixture : Bool := false) (counts : Array Nat := #[534,3172,1401]) : IO Unit := do
  try
    match gate with
    | "tree" => checkTree project d.root fixture
    | "schema" => Registry.schema d
    | "sources" => Registry.sources d
    | "order" => Registry.order d
    | "lifecycle" => Registry.lifecycle d
    | "registry" =>
      Registry.registryCore d
      if d.multi then
        runGate project ⟨"python3", #["scripts/check-content-amendments.py","--static",d.root.toString]⟩
    | "census" => Registry.census d fixture counts
    | "source-items" => Registry.items d
    | "policy" => Registry.policy d
    | _ => throw <| IO.userError "unknown data gate"
    if gate != "tree" then IO.println s!"check-{gate}: ok"
  catch error => throw <| IO.userError s!"check-{gate}: {error}"
/-- The shared native plan makes any failed data gate fatal before downstream execution. -/
def executeData (perform : String → IO Unit) : IO Unit := dataGates.forM perform
/-- Fixture and standalone callers retain each gate's former root and prerequisite contracts. -/
def dataEntry (project : System.FilePath) (gate : String) (args : List String) : IO Unit := do
  require (dataGates.contains gate) "unknown data gate"
  require (!(#["tree","census"].contains gate && args == ["--fixture"])) "invalid gate arguments: missing fixture root"
  let (fixture,target,countStrings) ← match args with
    | [] => pure (false,project.toString,[])
    | [target] => pure (false,target,[])
    | ["--fixture",target] => pure (true,target,[])
    | ["--fixture",target,a,b,c] => pure (true,target,[a,b,c])
    | _ => throw <| IO.userError "invalid gate arguments"
  require (!fixture || gate == "tree" || gate == "census") "fixture mode is explicit only for tree/census"
  require (countStrings.isEmpty || gate == "census") "only census accepts fixture counts"
  let root ← IO.FS.realPath target
  let mut counts := #[534,3172,1401]
  if !countStrings.isEmpty then
    require (Registry.digits countStrings[0]! true && Registry.digits countStrings[1]! && Registry.digits countStrings[2]!)
      "fixture counts must be nonnegative integers and pages must be positive"
    counts := countStrings.toArray.map String.toNat!
  if gate == "census" then
    if fixture then
      let some test ← IO.getEnv "LATTICE_TEST_ROOT" | throw <| IO.userError "fixture mode requires LATTICE_TEST_ROOT"
      let test ← IO.FS.realPath test
      validateTreeFixture (← IO.FS.realPath project).toString root.toString test.toString
    else require (trim (← git root #["rev-parse","--show-toplevel"]) == root.toString) "ROOT must be the repository top"
  if gate == "tree" then
    checkTree project root fixture
    return
  let modern ← (root / "registry/sources.tsv").pathExists
  let common := #["phase","pages","claims","slices","dependencies","bindings","claim-context","axioms","claim-axioms","claim-vocabulary-review","vocabulary","claim-vocabulary","modules","imports","statement-modules","statement-imports"]
  let names ← match gate with
    | "schema" => pure (Registry.headers.map (·.1))
    | "sources" => pure #["tracks","sources","source-progress","source-invariants"]
    | "order" => pure #["tracks","sources","pages","claims","dependencies"]
    | "lifecycle" => pure #["phase","sources","source-invariants","source-progress","claims","claim-vocabulary-review","vocabulary","claim-vocabulary"]
    | "source-items" => pure #["tracks","sources","pages","claims","source-items","item-claims"]
    | "registry" =>
      if modern then pure (Registry.headers.map (·.1))
      else
        let preliminary ← Registry.load root (common.push "reference")
        pure (common ++ #["reference"] ++ (if (preliminary.table "claim-context").rows.isEmpty then #[] else #["item-claims"]))
    | "census" =>
      let preliminary ← Registry.load root #["phase"]
      if Registry.phase preliminary == "bootstrap" then pure #["phase"]
      else if modern then pure (Registry.headers.map (·.1))
      else pure (#["phase","pages","claims","reference"] ++ (if Registry.phase preliminary == "census" then
        #["slices","dependencies","bindings","claim-context","axioms","claim-axioms","statement-modules","statement-imports"] else #[]))
    | "policy" =>
      let preliminary ← Registry.load root #["phase"]
      pure (if Registry.oneOf (Registry.phase preliminary) "census|vocabulary|skeleton" then
        #["phase","modules","statement-modules"] else #["phase"])
    | _ => throw <| IO.userError "unknown data gate"
  let d ← Registry.load root names
  if gate == "registry" && d.multi then
    Registry.schema d
    -- Bootstrap row rejection remains earlier than downstream foreign-key checks.
    if Registry.phase d == "bootstrap" then
      Registry.emptyTables d #["pages","claims","slices","dependencies","bindings","claim-context","axioms","claim-axioms","claim-vocabulary-review","vocabulary","claim-vocabulary","modules","imports","statement-modules","statement-imports"] "bootstrap requires"
    Registry.sources d; Registry.order d; Registry.lifecycle d
  if gate == "census" && d.multi && Registry.phase d != "bootstrap" then
    Registry.schema d; Registry.sources d; Registry.order d; Registry.lifecycle d
  dataCore project d gate fixture counts
/-- Run the tree first and load shared registry bytes lazily once for the remaining native plan. -/
def currentData (root : System.FilePath) : IO Registry.Data := do
  let cached ← IO.mkRef (none : Option Registry.Data)
  executeData fun gate => do
    if gate == "tree" then checkTree root root false
    else
      let d ← match ← cached.get with
        | some d => pure d
        | none =>
          let d ← Registry.load root
          cached.set (some d)
          pure d
      dataCore root d gate
  let some d ← cached.get | throw <| IO.userError "native data plan did not execute"
  pure d
/-- Compile this exact infrastructure source once for all fixture calls, then retire owned outputs even on failure. -/
def withNativeGates (root : System.FilePath) (use : Array (String × Option String) → IO Unit) : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    let before := trim (← git root #["hash-object","Checker/CheckAll.lean"])
    let sysroot ← toolchainRoot root
    let c := temporary / "CheckAll.c"; let executable := temporary / "check-all"
    runGate root ⟨(sysroot / "bin/lean").toString,
      #["-DwarningAsError=true","-c",c.toString,"Checker/CheckAll.lean"]⟩
    runGate root ⟨(sysroot / "bin/leanc").toString,
      #["--no-default-config","-o",executable.toString,c.toString]⟩
    require (trim (← git root #["hash-object","Checker/CheckAll.lean"]) == before) "native source changed during compilation"
    IO.println s!"check-all: fixture native source {before}; lean -DwarningAsError=true -c; leanc --no-default-config"
    use #[("LATTICE_CHECK_ALL_EXEC",some executable.toString),("LATTICE_CHECK_ALL_PROJECT",some root.toString)]
/-- Normalize only Lake's own environment, rejecting arbitrary fixture/executable overrides. -/
def validateOverrides (root : System.FilePath) : IO Unit := do
  let lakeKeys := #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN"]
  for key in overrides do
    if !lakeKeys.contains key then require ((← IO.getEnv key).isNone) s!"CI override forbidden: {key}"
  let declared := trim (← IO.FS.readFile (root / "lean-toolchain"))
  require ((← IO.getEnv "ELAN_TOOLCHAIN") == some declared) "noncanonical declared Elan toolchain"
  for key in #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"] do
    let expected ← IO.Process.output {
      cmd := "lake", args := #["env", "printenv", key], cwd := some root,
      env := lakeKeys.map (fun name => (name, none)) }
    require (expected.exitCode == 0 && (← IO.getEnv key) == some (trim expected.stdout))
      s!"noncanonical Lake environment: {key}"
/-- Parsed public CLI; no generic command or credential-injection option exists. -/
structure Options where
  /-- Current/full/CI/self-test. -/
  mode : String := ""
  /-- Explicit local comparison base. -/
  base : String := "origin/rewrite-main"
/-- Reject ambiguous or unsupported modes rather than silently selecting a partial check. -/
def options : List String → Options → Except String Options
  | [], o => if #["--current", "--full", "--ci", "--self-test"].contains o.mode then .ok o else .error "choose a mode"
  | "--base" :: base :: rest, o => options rest {o with base}
  | mode :: rest, o => if #["--current", "--full", "--ci", "--self-test"].contains mode && o.mode.isEmpty then
      options rest {o with mode} else .error "unknown or repeated mode"
/-- A failed or absent signature/evidence calculation leaves every regression required. -/
structure Selection where
  /-- Suite signatures, or null when inputs could not be established. -/
  sigs : Json := Json.null
  /-- Executable hash only when actually established. -/
  executable : String := ""
  /-- Validated runtime identity, or null. -/
  runtime : Json := Json.null
  /-- Only already-validated direct origins may populate this object. -/
  accepted : Json := Json.mkObj []
/-- The same fallback catches unavailable HTTP, malformed evidence and missing historical input. -/
def orFull (operation : IO Selection) : IO Selection := do
  try operation catch _ =>
    IO.println "check-all: accepted input evidence unavailable; execute required regressions"
    pure {}
/-- Compute CI selection without mutating or reusing partially established state on failure. -/
def calculateSelection (root : System.FilePath) (ctx : Json) (full : Bool) : IO Selection := do
  let runtime ← environment root
  let (sigs, executable) ← signatures root (← str ctx "head") runtime
  let mut accepted := Json.mkObj []
  if lookupAllowed full (← str ctx "event") then
    let repository ← env "GITHUB_REPOSITORY"
    let parts := split repository "/"
    require (parts.size == 2 && parts.all fun s => !s.isEmpty && s.toList.all fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-' || c == '.')) "invalid repository scope"
    let cache ← IO.mkRef #[]
    let e : Evidence := ⟨repository, ← env "GH_TOKEN", (← IO.monoMsNow) + 45000, executable, cache⟩
    accepted ← reuse root e ctx sigs runtime
  pure ⟨sigs, executable, runtime, accepted⟩

/-- Self-test assertion count, including expected rejection cases. -/
def expect (counter : IO.Ref Nat) (b : Bool) (name : String) : IO Unit := do
  require b ("self-test failed: " ++ name)
  counter.modify (·+1)
/-- A negative case passes only when the production validator actually rejects it. -/
def reject (counter : IO.Ref Nat) (action : IO α) (name : String) : IO Unit := do
  let failed ← try let _ ← action; pure false catch _ => pure true
  expect counter failed name
/-- Minimal valid synthetic receipt, independent of the actual mathematical corpus. -/
def fixtureReceipt : Json := Json.mkObj [
  ("version", toJson version), ("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)),
  ("head", toJson (String.ofList (List.replicate 40 'a'))),
  ("source_head", toJson (String.ofList (List.replicate 40 'c'))),
  ("base", toJson (String.ofList (List.replicate 40 'b'))),
  ("tree", toJson (String.ofList (List.replicate 40 'd'))), ("event", toJson "pull_request"),
  ("engine", toJson "engine"), ("environment", Json.mkObj []),
  ("current", toJson "success"), ("transition", toJson "success"), ("build", toJson "success"),
  ("suites", Json.mkObj (suites.toList.map fun (name, _) => (name, Json.mkObj [
    ("input", toJson (String.ofList (List.replicate 64 '1'))), ("result", toJson "executed"), ("origin", Json.null)])))]
/-- Native data/tree boundaries exercise production helpers independently of full runtime fixtures. -/
def selfTestData (root : System.FilePath) (count : IO.Ref Nat) : IO Unit := do
  for target in [:dataGates.size] do
    let visited ← IO.mkRef (#[] : Array String)
    reject count (executeData fun gate => do
      visited.modify (·.push gate)
      if gate == dataGates[target]! then throw <| IO.userError "injected data gate failure") "native data failure is fatal"
    expect count ((← visited.get).size == target + 1) "no native gate executes after failure"
  let absent : Registry.Data := ⟨root,#[]⟩
  reject count (Registry.order absent) "missing order tables do not pass vacuously"
  reject count (Registry.items absent) "missing item tables do not pass vacuously"
  reject count (Registry.lifecycle absent) "missing lifecycle tables do not pass vacuously"
  let phaseData : Registry.Data := ⟨root,#[ ("phase",Registry.tableFromText "phase\nvocabulary\textra\n") ]⟩
  expect count (Registry.phase phaseData == "vocabulary\textra") "phase reader preserves its entire record"
  reject count (Registry.phaseRead ⟨root,#[ ("phase",Registry.tableFromText "phase\nvocabulary") ]⟩) "unterminated second phase record rejected"
  reject count (dataEntry root "tree" ["--fixture"]) "tree fixture argument is explicit"
  reject count (dataEntry root "census" ["--fixture"]) "census fixture argument is explicit"
  let parsed := Registry.tableFromText "a\tb\nvalue\t\n"
  expect count (parsed.rows == #[#["value",""]]) "TSV trailing empty fields preserved"
  expect count ((Registry.tableFromText "a\nb").rows == #[#["b"]]) "unterminated final data row retained"
  expect count (!(Registry.tableFromText "a").headerEnded) "header LF remains required"
  for value in #["\r","x\u007f"," x","x "," x","x "] do
    expect count (!Registry.validField value) "C0 DEL and original edge whitespace rejected"
  for value in #["x y","\u0085x"," x"] do
    expect count (Registry.validField value) "C locale validation does not broaden to Unicode controls"
  expect count (Registry.slugify "A İ B" == "a-b") "ASCII-only source-item slug"
  expect count (Registry.digits "001" && !Registry.digits "001" true) "count and positive-position grammars differ"
  expect count (Registry.orderKey "000001.0001.0001.0001" &&
    !Registry.claimOrder "000001.0001.0001.0001") "order and registry-claim segment grammars differ"
  expect count (Registry.identifier "a'_1" && !Registry.identifier "1a" && !Registry.identifier "é") "ASCII Lean name grammar"
  let id := String.ofList (List.replicate 40 'a')
  let _ ← treeIndex ("100644 " ++ id ++ " 0\tREADME.md\u0000")
  expect count true "live index stage zero accepted"
  for record in #["120000 " ++ id ++ " 0\tREADME.md\u0000", "100644 " ++ id ++ " 2\tREADME.md\u0000", "100644 bad 0\tREADME.md\u0000"] do
    reject count (treeIndex record) "symlink unresolved index or malformed object rejected"
  let _ ← validateTreePaths #["LatticeSystem.lean"] #[] true
  expect count true "header-only bootstrap permits unregistered production root"
  reject count (validateTreePaths #["LatticeSystem.lean"] #["LatticeSystem.lean","LatticeSystem/Missing.lean"] true) "registered missing production module rejected"
  reject count (validateTreePaths #["LatticeSystem/Unknown.lean"] #[] true) "unregistered tracked production module rejected"
  for path in #["scripts/check-tree.sh","unexpected.txt","fixtures/x","tex/guide.tex"] do
    reject count (validateTreePaths #[path] #[] true) "closed tree rejects removed or unknown paths"
  validateTreeFixture "/project" "/test/fixture" "/test"
  expect count true "external fixture containment accepted"
  for (target,testRoot) in #[("/project","/project"),("/test/a","/"),("/project/tests/a","/project/tests"),("/outside/a","/test")] do
    reject count (validateTreeFixture "/project" target testRoot) "fixture source root ancestor and escape rejected"
  let reference := Registry.tableFromText <|
    "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes\nTASAKI2020\tref\t.v1\t" ++ id ++ "\t" ++ id ++ "\tpending\tnote\n"
  reject count (Registry.reference ⟨root,#[ ("reference",reference),("phase",Registry.tableFromText "phase\nbootstrap\n") ]⟩)
    "legacy edition starts with ASCII alphanumeric"
  let contexts := Registry.tableFromText "claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref\nCL-FIX-0002\t1\tCL-FIX-0001\tterm_reference\tinherited\treview\n"
  let claimHeader := ((Registry.headers.find? (·.1 == "claims")).map (·.2)).get!
  let claimRows := Registry.tableFromText (claimHeader ++ "\n" ++
    "CL-FIX-0001\tFIX\t000001.0001\tPG-FIX-0001\tsetup\tdefinition\tdefinition\tFixture setup.\t" ++ id ++ "\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n" ++
    "CL-FIX-0002\tFIX\t000001.0002\tPG-FIX-0001\towner\tassertion\ttheorem\tFixture assertion.\t" ++ id ++ "\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n")
  let contextData : Registry.Data := ⟨root,#[ ("claims",claimRows),("claim-context",contexts) ]⟩
  reject count (Registry.bindings contextData) "inherited context still requires item registry"
  let withItems := contextData.tables.push ("item-claims",Registry.tableFromText "item_id\tposition\tclaim_id\n")
  Registry.bindings {contextData with tables := withItems}
  expect count true "inherited context with an existing item registry otherwise passes"

/-- Fast negative and positive tests cover dispatch, schema, ancestry, scope and secrecy. -/
def selfTest (root : System.FilePath) : IO Unit := do
  let count ← IO.mkRef 0
  selfTestData root count
  expect count ((Json.mkObj [("z", toJson "last"), ("a", toJson "first")]).compress ==
    (Json.mkObj [("a", toJson "first"), ("z", toJson "last")]).compress) "canonical JSON key order"
  for status in #["A", "D", "T", "R100"] do
    expect count (changeForcesFull "README.md" status "100644" "100644" false) "all raw endpoints"
  for (path, oldMode, newMode, header) in #[
    ("unknown", "100644", "100644", false), ("registry/new.tsv", "100644", "100644", false),
    ("README.md", "100644", "100755", false), ("README.md", "100644", "120000", false),
    ("registry/claims.tsv", "100644", "100644", true),
    ("registry/bindings.tsv", "100644", "100644", false),
    ("Checker/CheckAll.lean", "100644", "100644", false)] do
    expect count (changeForcesFull path "M" oldMode newMode header) "full fallback input"
  expect count (!changeForcesFull "registry/claims.tsv" "M" "100644" "100644" false) "known corpus edit"
  expect count (policyProjection "README.md" "exact PR exact head SHA prose" ==
    policyProjection "README.md" "different prose exact PR exact head SHA") "policy prose projection"
  expect count (policyProjection "README.md" "no gate" != policyProjection "README.md" "exact PR exact head SHA") "policy predicates"
  for (phase, rows, needed) in #[("bootstrap", 1, false), ("vocabulary", 1, true), ("census", 2, true)] do
    expect count ((currentPlan root phase rows).any (·.cmd == "scripts/check-vocabulary.sh") == needed) "semantic current selection"
  for mode in #["--current", "--full", "--ci", "--self-test"] do
    expect count ((options [mode] {}).isOk) "known CLI mode"
  for args in [[], ["--current", "--full"], ["--unknown"], ["--base"]] do
    expect count (!(options args {}).isOk) "invalid CLI rejected"
  validReceipt fixtureReceipt
  expect count true "valid receipt"
  reject count (validReceipt (fixtureReceipt.setObjVal! "version" (toJson (2 : Nat)) )) "previous v2 receipt cannot be v3 evidence"
  for fieldName in #["version", "head", "source_head", "base", "tree", "current", "transition", "build", "suites"] do
    reject count (validReceipt (fixtureReceipt.setObjVal! fieldName Json.null)) "missing or invalid receipt field"
  reject count (validReceipt (fixtureReceipt.setObjVal! "version" (toJson (1 : Nat)))) "old schema cannot be evidence"
  reject count (validReceipt (fixtureReceipt.setObjVal! "extra" Json.null)) "unknown receipt field"
  let run := Json.mkObj [("id", toJson (7 : Nat)), ("status", toJson "completed"), ("conclusion", toJson "success"),
    ("name", toJson "rewrite-ci"), ("path", toJson ".github/workflows/rewrite-ci.yml"),
    ("repository", Json.mkObj [("full_name", toJson "owner/repo")]), ("event", toJson "pull_request"),
    ("run_attempt", toJson (2 : Nat)), ("head_sha", ← field fixtureReceipt "source_head")]
  let _ ← validateRun run "owner/repo" 7
  for (key, value) in #[("status", "in_progress"), ("conclusion", "cancelled"), ("conclusion", "failure"),
    ("conclusion", "skipped"), ("name", "other"), ("path", "other.yml"), ("event", "workflow_dispatch")] do
    reject count (validateRun (run.setObjVal! key (toJson value)) "owner/repo" 7) "unsuccessful or foreign producer"
  reject count (validateRun run "foreign/repo" 7) "foreign repository"
  let job := Json.mkObj [("id", toJson (11 : Nat)), ("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)),
    ("name", toJson "verify"), ("status", toJson "completed"), ("conclusion", toJson "success")]
  let _ ← validateJob job 7 2
  for result in #["cancelled", "skipped", "failure", "timed_out", "neutral"] do
    reject count (validateJob (job.setObjVal! "conclusion" (toJson result)) 7 2) "job must actually succeed"
  reject count (validateJob job 7 1) "attempt mismatch"
  reject count (validateJob job 8 2) "run mismatch"
  validateIdentity fixtureReceipt run 7 2 "engine"
  for changed in #[fixtureReceipt.setObjVal! "run_id" (toJson (8 : Nat)),
    fixtureReceipt.setObjVal! "source_head" (← field fixtureReceipt "head"),
    fixtureReceipt.setObjVal! "engine" (toJson "foreign")] do
    reject count (validateIdentity changed run 7 2 "engine") "receipt producer binding"
  let base ← str fixtureReceipt "base"; let source ← str fixtureReceipt "source_head"; let actualTree ← str fixtureReceipt "tree"
  validateCheckout fixtureReceipt #[base, source] actualTree
  reject count (validateCheckout fixtureReceipt #[base] actualTree) "wrong synthetic parent"
  reject count (validateCheckout (fixtureReceipt.setObjVal! "head" (toJson source)) #[base, source] actualTree) "direct PR head rejected"
  reject count (validateCheckout fixtureReceipt #[base, source] base) "tree mismatch"
  let plan := currentPlan root "vocabulary" 3 ++
    #[⟨"scripts/check-base-diff-ci.sh", #[root.toString, base]⟩] ++
    suites.map (fun (_, script) => ⟨"scripts/" ++ script, #[root.toString]⟩) ++ #[⟨"lake", #["build"]⟩]
  for target in [:plan.size] do
    let calls ← IO.mkRef 0
    reject count (execute (fun _ => do
      let index ← calls.get; calls.modify (·+1)
      require (index != target) "injected selected failure") plan) "every current/selected failure propagates"
    expect count ((← calls.get) == target + 1) "no commands after failed gate"
  let cache ← IO.mkRef #[]
  let e : Evidence := ⟨"owner/repo", "fixture", 0, "engine", cache⟩
  reject count (http root e "/actions/runs/7") "expired lookup does not contact network"
  reject count (output root "sh" #["-c", "exit 7"]) "external exit is mandatory"
  expect count (pushBound source base source #[base]) "push actual before"
  expect count (!pushBound source source source #[base]) "origin equal HEAD is not push before"
  expect count (!pushBound source (String.ofList (List.replicate 40 '0')) source #[base]) "zero before rejected"
  expect count (!pushBound source base source #[base, source]) "ambiguous push parents rejected"
  let _ ← receiptFromLog ("timestamp " ++ marker ++ fixtureReceipt.compress)
  for text in #["no marker", marker ++ "invalid", marker ++ fixtureReceipt.compress ++ "\n" ++ marker ++ fixtureReceipt.compress] do
    reject count (receiptFromLog text) "missing malformed duplicate marker"
  expect count (!lookupAllowed true "pull_request" && lookupAllowed true "push") "new PR engine full and exact postmerge lookup"
  let ctx := Json.mkObj [("event", toJson "push"), ("base", toJson base), ("tree", toJson actualTree)]
  let envJson ← field fixtureReceipt "environment"
  expect count (← candidateBound fixtureReceipt ctx source envJson) "exact postmerge candidate"
  expect count (!(← candidateBound fixtureReceipt ctx base envJson)) "different source same tree rejected"
  expect count (!(← candidateBound fixtureReceipt (ctx.setObjVal! "base" (toJson source)) source envJson)) "actual before mismatch"
  let origin := Json.mkObj [("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)), ("job_id", toJson (11 : Nat))]
  let original : Loaded := ⟨fixtureReceipt, origin⟩
  let signature := String.ofList (List.replicate 64 '1')
  expect count (← originalBound original origin "skeleton" signature envJson) "direct executed original"
  for key in #["run_attempt", "job_id"] do
    expect count (!(← originalBound original (origin.setObjVal! key (toJson (99 : Nat))) "skeleton" signature envJson)) "original job or attempt mismatch"
  let recursive := fixtureReceipt.setObjVal! "suites" <|
    (fixtureReceipt.getObjValD "suites").setObjVal! "skeleton" <| Json.mkObj [
      ("input", toJson signature), ("result", toJson "reused"), ("origin", origin)]
  expect count (!(← originalBound ⟨recursive, origin⟩ origin "skeleton" signature envJson)) "recursive original rejected"
  expect count (!(← originalBound original origin "skeleton" "other" envJson)) "original input mismatch"
  for label in #["API unavailable", "historical fixture unavailable"] do
    let selected ← orFull (throw <| IO.userError label)
    expect count (suites.all fun (name, _) => regressionRequired "--ci" selected.accepted name) "lookup and history failure require all suites"
  let allAccepted := Json.mkObj (suites.toList.map fun (name, _) => (name, origin))
  expect count (suites.all fun (name, _) => !regressionRequired "--current" allAccepted name) "current coverage stays partial"
  expect count (suites.all fun (name, _) => regressionRequired "--full" allAccepted name) "explicit full cannot reuse"
  let rows : Array Entry := #[⟨"Checker/CheckAll.lean", "100644", "blob", "engine"⟩,
    ⟨".gitignore", "100644", "blob", "ignore"⟩, ⟨"registry/claims.tsv", "100644", "blob", "old"⟩]
  let headers := Json.mkObj [("registry/claims.tsv", toJson "header")]
  let policy := Json.mkObj [("README.md", policyProjection "README.md" "exact PR exact head SHA")]
  let registryA := Json.mkObj [("registry/claims.tsv", toJson "old")]
  let registryB := Json.mkObj [("registry/claims.tsv", toJson "new")]
  let (before, _) ← payloads root rows headers registryA policy (Json.mkObj []) envJson
  let (after, _) ← payloads root rows headers registryB policy (Json.mkObj []) envJson
  for (name, _) in suites do
    expect count ((before.getObjValD name == after.getObjValD name) ==
      (!#["checkers", "corrections", "content"].contains name)) "corpus copy closure and synthetic projection"
  let compilerEnvironment := envJson.setObjVal! "native_compiler" (toJson "changed toolchain backend")
  let (compilerInputs, _) ← payloads root rows headers registryA policy (Json.mkObj []) compilerEnvironment
  expect count (suites.all fun (name, _) => before.getObjValD name != compilerInputs.getObjValD name) "native compiler identity changes every actual input"
  let changedRows := rows.set! 1 ⟨".gitignore", "100644", "blob", "changed"⟩
  let (changed, _) ← payloads root changedRows headers registryA policy (Json.mkObj []) envJson
  expect count (suites.all fun (name, _) => before.getObjValD name != changed.getObjValD name) "gitignore is executable fixture input"
  let changedHeaders := headers.setObjVal! "registry/claims.tsv" (toJson "new header")
  let (changed, _) ← payloads root rows changedHeaders registryA policy (Json.mkObj []) envJson
  expect count (suites.all fun (name, _) => before.getObjValD name != changed.getObjValD name) "registry schema closure"
  let transport := curlArguments "owner/repo" "/actions/jobs/11/logs"
  expect count (transport[0]! == "--disable" && transport.contains "--proto-redir" &&
    !transport.contains "--location-trusted" && !transport.any (fun x => (x.splitOn "Authorization").length > 1)) "curl configuration and credential boundary"
  let badToken : Evidence := ⟨"owner/repo", "invalid\ncredential", (← IO.monoMsNow) + 45000, "engine", cache⟩
  reject count (http root badToken "/actions/runs/7") "credential config injection rejected before HTTP"
  IO.println s!"check-all self-test: {(← count.get)} positive/negative assertions passed"

/-- Execute one mode; CI evidence cannot replace fresh data/transition/build gates. -/
def dispatch (root : System.FilePath) (o : Options) : IO Unit := do
  selfTest root
  if o.mode == "--self-test" then return
  let mut ctx := Json.null
  let mut base := o.base
  let mut selection : Selection := {}
  if o.mode == "--ci" then
    validateOverrides root
    ctx ← context root
    base ← str ctx "base"
    let head ← str ctx "head"
    let full ← fullRequired root base head
    selection ← orFull (calculateSelection root ctx full)
  else base ← commit root base
  let sigs := selection.sigs; let executable := selection.executable
  let runtime := selection.runtime; let accepted := selection.accepted
  let current ← currentData root
  let phase := Registry.phase current
  let moduleRows := (current.table "modules").records.size
  execute (runGate root) (currentPlan root phase moduleRows)
  runGate root ⟨"scripts/check-base-diff-ci.sh", #[root.toString, base]⟩
  let mut results := Json.mkObj []
  if o.mode != "--current" then
    let perform := fun childEnvironment => do
      for (name, script) in suites do
        if regressionRequired o.mode accepted name then
          runGate root ⟨"scripts/" ++ script, #[root.toString]⟩ childEnvironment
        else
          let origin := accepted.getObjValD name
          IO.println s!"check-all: reuse {name} from run {← nat origin "run_id"} job {← nat origin "job_id"}"
    if suites.any (fun (name, _) => regressionRequired o.mode accepted name) then
      withNativeGates root perform
    else perform #[]
    for (name, _) in suites do
      let origin := accepted.getObjValD name
      results := results.setObjVal! name <| Json.mkObj [
        ("input", sigs.getObjValD name), ("result", toJson (if origin.isNull then "executed" else "reused")), ("origin", origin)]
  runGate root ⟨"lake", #["build"]⟩
  if o.mode == "--ci" && !sigs.isNull && !runtime.isNull && !executable.isEmpty then
    let receipt := ctx.mergeObj <| Json.mkObj [("version", toJson version),
      ("run_id", toJson ((← env "GITHUB_RUN_ID").toNat!)),
      ("run_attempt", toJson ((← env "GITHUB_RUN_ATTEMPT").toNat!)),
      ("engine", toJson executable), ("environment", runtime), ("suites", results),
      ("current", toJson "success"), ("transition", toJson "success"), ("build", toJson "success")]
    IO.println (marker ++ receipt.compress)
  IO.println (if o.mode == "--current" then
    "check-all: current gates passed; regression acceptance remains required in CI"
    else "check-all: all selected gates passed")

end Checker.CheckAll

/-- Standalone Lean verification entrypoint; any selected failure makes the job fail. -/
def main (args : List String) : IO UInt32 := do
  try
    let root ← IO.currentDir
    match args with
    | "--gate" :: gate :: rest =>
      let project := (← IO.getEnv "LATTICE_CHECK_ALL_PROJECT").getD root.toString
      Checker.CheckAll.dataEntry project gate rest
    | _ =>
      let o ← IO.ofExcept <| Checker.CheckAll.options args {}
      Checker.CheckAll.dispatch root o
    return 0
  catch error =>
    IO.eprintln s!"check-all: failed: {error}"
    return 1
