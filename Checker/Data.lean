import Checker.Content
import Checker.Support

/-! Native registry, tree and policy validators. -/
namespace Checker.CheckAll
open Lean

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
  "Checker/Content.lean", "Checker/Publication.lean", "Checker/Bootstrap.lean", "Checker/Tests/Publication.lean",
  "Checker/Text.lean", "Checker/Publication/Tabular.lean", "Checker/Publication/Items.lean",
  "Checker/Publication/Catalog.lean", "Checker/Publication/Render.lean",
  "docs/index.md", "docs/generated/index.md", "docs/generated/catalog.json",
  "Checker/BaseDiff.lean",
  "Checker/CheckAll.lean",
  "Checker/Corrections.lean",
  "Checker/Data.lean",
  "Checker/History.lean",
  "Checker/Inputs.lean",
  "Checker/LakeIsolation.lean",
  "Checker/Main.lean",
  "Checker/Regressions.lean",
  "Checker/Selector.lean",
  "Checker/Semantic.lean",
  "Checker/SemanticDriver.lean",
  "Checker/Skeleton.lean",
  "Checker/Support.lean",
  "Checker/TestSupport.lean",
  "Checker/Tests/BaseDiff.lean",
  "Checker/Tests/Content.lean",
  "Checker/Tests/Corrections.lean",
  "Checker/Tests/FixtureSupport.lean",
  "Checker/Tests/Fixtures.lean",
  "Checker/Tests/Multisource.lean",
  "Checker/Tests/Registry.lean",
  "Checker/Tests/Selector.lean",
  "Checker/Tests/SkeletonComposed.lean",
  "Checker/Tests/SkeletonFixture.lean",
  "Checker/Tests/SkeletonPure.lean",
  "Checker/Tests/TreePolicy.lean",
  "Checker/Tests/Vocabulary.lean",
  "Checker/Transition.lean",
  "Checker/Vocabulary.lean"]
/-- Only registered production modules and established generated catalog families extend the closed tree. -/
def allowedTreePath (registered : Array String) (path : String) : Bool :=
  fixedTreePaths.contains path ||
  (#["docs/generated/groups/", "docs/generated/sources/", "docs/generated/tracks/"].any
    (path.startsWith ·) && path.endsWith ".md") ||
  (path.startsWith "LatticeSystem/" && path.endsWith ".lean" && registered.contains path)
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
    require (!(col r 3).isEmpty) "empty track title"
    require (slug (col r 4)) "bad track public slug"
  require (!ss.isEmpty) "no sources registered"
  unique ss #[1] "duplicate source ID"; unique ss #[5] "duplicate citation key"; unique ss #[13] "duplicate source public slug"
  contiguous ss 2 3 "source positions are not contiguous"
  let mut previous := ""
  for r in ss do
    require (sourceId (col r 1)) "bad source ID"
    require (d.has "tracks" (col r 2)) "unknown source track"
    require (oneOf (col r 4) "book|paper|preprint|other") "bad source kind"
    require (token (col r 5)) "bad citation key"
    require (!(col r 6).isEmpty && !(col r 7).isEmpty) "empty source title or authors"
    require (digits (col r 8) && (col r 8).length == 4) "bad source year"
    require (!(col r 9).isEmpty) "empty source edition"
    require (oneOf (col r 10) "isbn|doi|arxiv|none") "bad identifier kind"
    require (if col r 10 == "none" then col r 11 == "NONE" && col r 12 == "NONE" else
      !(col r 11).isEmpty && col r 11 != "NONE" && (col r 12).startsWith "https://")
      (if col r 10 == "none" then "none identifier requires NONE value and URL" else "identified source requires identifier and HTTPS public URL")
    require (slug (col r 13)) "bad source public slug"
    require (!(col r 14).isEmpty) "empty local reference key"
    require (((col r 15).isEmpty == (col r 16).isEmpty) && ((col r 15).isEmpty ||
      (oid (col r 15) && oid (col r 16) && (col r 15).length == (col r 16).length))) "source OIDs must transition atomically with equal width"
    require (oneOf (col r 17) "pending|pass1|pass2|reconciled|frozen") "bad source coverage"
    let key := globalKey d (col r 1) ""
    require (previous.isEmpty || previous < key) "sources are not in global track order"
    previous := key
  let progress := (d.table "source-progress").rows
  unique progress #[1] "duplicate source progress"
  for r in progress do
    require (!(d.sourceRow (col r 1)).isEmpty) "unknown progress source"
    require (oneOf (col r 2) "registered|source_frozen|census_pass1|census_pass2|census_reconciled|vocabulary_reviewed|skeleton_frozen|proof_active|complete") "bad source lifecycle"
    require (token (col r 3)) "bad source progress review token"
  require (ss.all fun r => has progress (col r 1)) "source lacks progress row"
  let invariants := (d.table "source-invariants").rows
  unique invariants #[1] "duplicate source invariant"
  for r in invariants do
    require (!(d.sourceRow (col r 1)).isEmpty) "unknown invariant source"
    require (digits (col r 2) true && (#[3,4,5,6].all fun n => digits (col r n))) "bad source invariant count"
    require ((col r 4).toNat! ≤ (col r 3).toNat!) "formalization target count exceeds active claim count"
    require ((col r 6).toNat! ≤ (col r 2).toNat!) "no-claim page count exceeds physical page count"
    require (oid (col r 7)) "bad census OID"
    require (token (col r 8)) "bad invariant review token"

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
    let mut failures : Array String := #[]
    let mut previous := ""
    let mut lastLocal : Std.HashMap String String := {}
    for r in (d.table table).rows do
      let pageMode := table == "pages"
      let stem := (if pageMode then "PG-" else "CL-") ++ col r 2 ++ "-"
      let suffix := ((col r 1).drop stem.length).toString
      if !((col r 1).startsWith stem && digits suffix && suffix.length ≥ 4) then
        failures := failures.push (if pageMode then "page ID/source mismatch" else "claim ID/source mismatch")
      if pageMode then
        if (d.sourceRow (col r 2)).isEmpty then failures := failures.push "unknown page source"
        if !(digits (col r 3) && (col r 3).length == 6) then failures := failures.push "bad page order key"
      else
        let page := d.row "pages" (col r 4)
        if (d.sourceRow (col r 2)).isEmpty || page.isEmpty || col page 2 != col r 2 then
          failures := failures.push "claim source/page mismatch"
        if !orderKey (col r 3) then failures := failures.push "bad claim order key"
        if !page.isEmpty && ((col r 3).take 6).toString != col page 3 then
          failures := failures.push "claim/page order mismatch"
      if let some prior := lastLocal[col r 2]? then
        if col r 3 ≤ prior then
          failures := failures.push (if pageMode then "page order is not strictly increasing" else "claim order is not strictly increasing")
      let key := globalKey d (col r 2) (col r 3)
      if !previous.isEmpty && key ≤ previous then
        failures := failures.push (if pageMode then "page rows are not in global source order" else "claim rows are not in global source order")
      lastLocal := lastLocal.insert (col r 2) (col r 3)
      previous := key
    require failures.isEmpty (String.intercalate "\n" failures.toList ++ "\n" ++
      (if table == "pages" then "page identity or order invalid" else "claim identity or order invalid"))
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
    require (col r 7 == "PENDING" || oid (col r 7)) "bad statement type OID"
    require (col r 8 == "PENDING" || oid (col r 8)) "bad statement value OID"
    require (oneOf (col r 9) "proof_stub|definitional") "bad implementation status"
    if proof then
      require (name (col r 3) && col r 10 == "theorem" && (col r 11 == "PENDING" || oid (col r 11))) "proof stub metadata is incomplete"
      if phase d == "proof" then
        require (col r 12 == "NONE" || oid (col r 12)) "bad R5 proof value OID"
      else require (col r 12 == "NONE") "R4 proof stub value OID must be NONE"
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
    require (oneOf (col r 4) "assumption|term_reference") "bad claim-context use kind"
    require (oneOf (col r 5) "same_item|inherited") "bad claim-context scope"
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
    require (col r 7 == "PENDING" || oid (col r 7)) "bad vocabulary type OID"
    require (col r 8 == "PENDING" || oid (col r 8)) "bad vocabulary declaration OID"
    require (oneOf (col r 9) "graph_core|finite_volume|linear_algebra|operator_algebra|quantum_state|stat_mech|fermion|generated") "bad vocabulary design role"
    require (oneOf (col r 10) "none|local_operation|explicit_finite_volume|inherited") "bad vocabulary finiteness scope"
    if col r 5 == "primary" then
      require (col r 6 == "NONE") "primary vocabulary must use parent NONE"
      require (col r 9 != "generated" && col r 10 != "inherited") "primary vocabulary cannot use generated metadata"
    else
      require (col r 6 != "NONE" && !(col r 6).isEmpty && col r 6 != id) "generated vocabulary needs a distinct parent"
      require (col (d.row "vocabulary" (col r 6)) 5 == "primary") "unknown or non-primary vocabulary parent"
      require (oneOf (col r 4) "constructor|recursor|projection") "generated vocabulary has a non-generated declaration kind"
      require (col r 9 == "generated" && col r 10 == "inherited") "generated vocabulary needs generated/inherited metadata"
    require (previous.isEmpty || previous < id) "vocabulary IDs are not strictly increasing"
    previous := id
    require (col (d.row "modules" (col r 3)) 3 == "leaf") "vocabulary declaration needs a registered leaf module"
  for r in (d.table "claim-vocabulary-review").rows do
    require (d.has "claims" (col r 1)) "unknown vocabulary-review claim"
    require (col (d.row "claims" (col r 1)) 12 == "false") "tombstoned claim has vocabulary review"
    require (oneOf (col r 2) "mathlib_only|project_vocabulary") "bad vocabulary basis"
    require (token (col r 3)) "bad vocabulary review token"
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
    require (!(col r 7).isEmpty) "empty item title"
    require (!(col r 8).isEmpty) "empty item locator"
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
    require (!item.isEmpty) "unknown item relation"
    require (!claim.isEmpty) "unknown item claim"
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
        discard <| Checker.Content.validateStatic d.root
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

end Checker.CheckAll
