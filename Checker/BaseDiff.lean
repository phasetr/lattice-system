import Checker.Data

/-! Monotone registry-history validation against an explicit directory or verified Git base. -/
namespace Checker.BaseDiff
open Lean System Checker.CheckAll
open Checker.CheckAll.Registry

/-- Exact files of a registry revision, including the legacy reference table when present. -/
structure Snapshot where
  /-- Physical blobs and true absence are retained for immutable provenance and ledger prefixes. -/
  files : Std.HashMap String String := {}
  /-- Explicit schema views never replace the observed physical blobs. -/
  views : Std.HashMap String String := {}
  /-- Directory-base reads historically used line-printing AWK; Git-base reads used exact blobs. -/
  normalizeLines : Bool := false

/-- Read a directory's table bytes without interpreting an absent table as an empty artifact. -/
def snapshot (root : FilePath) (profile : Checker.RegistryLayout.Profile := .historical) : IO Snapshot := do
  let result ← (← (root / "registry").readDir).foldlM (fun (result : Snapshot) entry => do
    if entry.path.extension == some "tsv" then
      return {files := result.files.insert ("registry/" ++ entry.fileName) (← IO.FS.readFile entry.path)}
    else return result) {}
  let result ← if ← (root / "references/tasaki-2020.tsv").pathExists then
    pure {result with files := result.files.insert "references/tasaki-2020.tsv" (← IO.FS.readFile (root / "references/tasaki-2020.tsv"))}
    else pure result
  let view ← Checker.RegistryLayout.normalize result.files profile
  return {result with views := view.files}

/-- Read a semantic table while keeping physical membership separately available in `files`. -/
def Snapshot.text (snapshot : Snapshot) (path : String) : Option String :=
  snapshot.views[path]? <|> snapshot.files[path]?

/-- A semantic schema view can be available without asserting physical historical existence. -/
def Snapshot.hasTable (snapshot : Snapshot) (path : String) : Bool :=
  (snapshot.text path).isSome

/-- Extract data records using the old line-based TSV interpretation. -/
def records (text : String) : Array Row := (tableFromText text).rows

/-- Canonical header for the explicitly supported empty-infrastructure migrations. -/
def emptyHeader (path : String) : Option String := do
  let stem ← path.dropPrefix? "registry/"
  let stem ← stem.toString.dropSuffix? ".tsv"
  let (_, header) ← headers.find? (·.1 == stem.toString)
  return header ++ "\n"

/-- Frozen compatibility defaults for the supported pre-multisource rewrite fixtures. -/
def compatibilityDefault (path : String) : Option String :=
  match path with
    | "registry/tracks.tsv" => some "track_id\tposition\ttitle\tpublic_slug\nTR-TASAKI\t1\tTasaki front-to-back\ttasaki\n"
    | "registry/sources.tsv" => some "source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage\nTASAKI2020\tTR-TASAKI\t1\tbook\tTASAKI2020\tPhysics and Mathematics of Quantum Many-Body Systems\tHal Tasaki\t2020\t2020.springer.ebook.9783030412654\tdoi\t10.1007/978-3-030-41265-4\thttps://doi.org/10.1007/978-3-030-41265-4\ttasaki-2020\tHal.Tasaki.P534.Physics_and_Mathematics_of_Quantum_Many_Body_Systems.pdf\t91d1237a6384d470bcdc453f058f8e08603767c5\t342ef0ce220dd3ed1c6cc0cdfab5a4d86bbd044f\tfrozen\n"
    | "registry/source-invariants.tsv" => some "source_id\tphysical_page_count\tactive_claim_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref\nTASAKI2020\t534\t3172\t1401\t63\tf65e4f7c57b2ef82e71156c147d3539609e02074\tR2-CENSUS-RECONCILED\n"
    | "registry/source-progress.tsv" => some "source_id\tlifecycle\treview_ref\nTASAKI2020\tvocabulary_reviewed\tVOCABULARY-INDEPENDENT-REVIEW\n"
    | _ => none

/-- Resolve the finite set of old empty infrastructure tables, never arbitrary missing input. -/
def baseline (before : Snapshot) (path : String) (modern : Bool) : IO String := do
  let initial ← match before.text path with
    | some text => pure text
    | none =>
      if let some text := compatibilityDefault path then return text
      require (#["registry/claim-vocabulary-review.tsv", "registry/vocabulary.tsv",
        "registry/claim-vocabulary.tsv", "registry/modules.tsv", "registry/imports.tsv",
        "registry/claim-context.tsv", "registry/statement-modules.tsv",
        "registry/statement-imports.tsv", "registry/claim-content-amendments.tsv",
        "registry/claim-location-amendments.tsv"].contains path)
        s!"base missing {path}"
      let some text := emptyHeader path | throw <| IO.userError s!"base missing {path}"
      pure text
  let text := if before.normalizeLines then
    String.join <| (tableFromText initial).records.toList.map (· ++ "\n") else initial
  if modern && path == "registry/claim-vocabulary-review.tsv" then
    return String.join <| (tableFromText text).records.toList.map fun line =>
      let row := split line "\t"
      String.intercalate "\t" (if row[2]?.getD "" == "R3-INDEPENDENT-REVIEW-P0" then
        (row.set! 2 "VOCABULARY-INDEPENDENT-REVIEW").toList else row.toList) ++ "\n"
  return text

/-- Retain the old last-record semantics for stable-ID projections. -/
def index (rows : Array Row) : Std.HashMap String Row :=
  rows.foldl (fun result row => result.insert (col row 1) row) {}

/-- Project exactly the named one-based columns. -/
def projection (row : Row) (columns : Array Nat) : Array String := columns.map (col row)

/-- Compare rows as a set, as the old associative-array guards did. -/
def sameRows (before after : Array Row) : Bool :=
  before.all after.contains && after.all before.contains

/-- Verify a collection's original stable identities remain present. -/
def noDeletion (before after : Array Row) (path : String) : IO Unit := do
  let current := index after
  let missing := before.filter fun row => !current.contains (col row 1)
  require missing.isEmpty (String.intercalate "\n" (missing.toList.map fun row => "deleted stable ID " ++ col row 1) ++ s!"\n{path} stable-ID deletion")

/-- Freeze specified existing columns, allowing genuinely new stable identities. -/
def compareColumns (before after : Array Row) (columns : Array Nat) (path label : String) : IO Unit := do
  let old := index before
  let changed := after.filter fun row => match old[col row 1]? with
    | none => false
    | some prior => projection prior columns != projection row columns
  require changed.isEmpty (String.intercalate "\n" (changed.toList.map fun row => s!"{label} changed for {col row 1}") ++ s!"\n{path} {label} regression")

/-- Require previous relation records without freezing the order of independent relations. -/
def oldRows (before after : Array Row) (path label : String) : IO Unit :=
  require (before.all after.contains) s!"{label} disappeared or drifted\n{path} {label} regression"

/-- Apply monotone OID finalization to an existing one-based field. -/
def oidAdvance (old current : String) : Bool :=
  if old == "PENDING" then current == "PENDING" || oid current else oid old && current == old

/-- Ordered page census states are monotone. -/
def passRank (value : String) : Nat :=
  if value == "pending" then 1 else if value == "disputed" then 2 else if value == "complete" then 3 else 0

/-- Reference observation stages are independent from source lifecycle stages. -/
def coverageRank (value : String) : Nat :=
  if oneOf value "pending|pass1|pass2|reconciled|frozen" then
    #["", "pending", "pass1", "pass2", "reconciled", "frozen"].idxOf value else 0

/-- Global capability rank, with unknown values retaining the original zero rank. -/
def phaseRank (value : String) : Nat :=
  if oneOf value "bootstrap|census|vocabulary|skeleton|proof" then
    #["", "bootstrap", "census", "vocabulary", "skeleton", "proof"].idxOf value else 0

/-- Full source lifecycle rank used only by the monotonicity guard. -/
def lifecycleRank (value : String) : Nat :=
  if oneOf value "registered|source_frozen|census_pass1|census_pass2|census_reconciled|vocabulary_reviewed|skeleton_frozen|proof_active|complete" then
    #["", "registered", "source_frozen", "census_pass1", "census_pass2", "census_reconciled", "vocabulary_reviewed", "skeleton_frozen", "proof_active", "complete"].idxOf value else 0

/-- Ordinary history constraints, with the dedicated reviewed event owning its exception. -/
def validate (before current : Snapshot) (allowSupersession replay : Bool) (event : String) : IO Unit := do
  let modern := current.files.contains "registry/sources.tsv"
  let readOld := fun path => baseline before path modern
  let readCurrent := fun path => do
    let some text := current.text path | throw <| IO.userError s!"current missing {path}"
    pure text
  let rowsOld := fun path => records <$> readOld path
  let rowsCurrent := fun path => records <$> readCurrent path
  for path in #["registry/phase.tsv","registry/pages.tsv","registry/claims.tsv","registry/slices.tsv",
    "registry/dependencies.tsv","registry/bindings.tsv","registry/axioms.tsv","registry/claim-axioms.tsv"] do
    require (before.hasTable path) s!"base missing {path}"
    discard <| readCurrent path
  if !modern then
    require (before.files.contains "references/tasaki-2020.tsv") "base missing references/tasaki-2020.tsv"
    discard <| readCurrent "references/tasaki-2020.tsv"
  for path in #["claim-vocabulary-review","vocabulary","claim-vocabulary","modules","imports",
    "claim-context","statement-modules","statement-imports"] do
    discard <| readCurrent ("registry/" ++ path ++ ".tsv")
  if modern then
    for path in #["tracks","sources","source-invariants","source-progress","source-items","item-claims"] do
      discard <| readCurrent ("registry/" ++ path ++ ".tsv")
  for stem in #["pages","claims","axioms","vocabulary","modules","statement-modules"] do
    let path := "registry/" ++ stem ++ ".tsv"
    noDeletion (← rowsOld path) (← rowsCurrent path) path
  if !replay then
    noDeletion (← rowsOld "registry/claim-vocabulary-review.tsv") (← rowsCurrent "registry/claim-vocabulary-review.tsv") "registry/claim-vocabulary-review.tsv"
  let identity := if modern then #["tracks","sources","source-invariants","source-progress"] else #[]
  for stem in identity do
    let path := "registry/" ++ stem ++ ".tsv"
    noDeletion (← rowsOld path) (← rowsCurrent path) path
  if modern && before.files.contains "registry/source-items.tsv" then
    noDeletion (← rowsOld "registry/source-items.tsv") (← rowsCurrent "registry/source-items.tsv") "registry/source-items.tsv"
  if !modern then
    noDeletion (← rowsOld "references/tasaki-2020.tsv") (← rowsCurrent "references/tasaki-2020.tsv") "references/tasaki-2020.tsv"
  let compare := fun path columns label => do
    compareColumns (← rowsOld path) (← rowsCurrent path) columns path label
  compare "registry/pages.tsv" #[2,3,4,5,6,7] "identity/order/locator"
  unless replay do
    compare "registry/claims.tsv" (if allowSupersession then #[2,3,4,5,6,7,8,10,11] else #[2,3,4,5,6,7,8,10,11,12,13,14,15])
      (if allowSupersession then "identity/order/locator/content/exclusion" else "identity/order/locator/content/exclusion/supersession")
  compare "registry/axioms.tsv" #[2,3,4,5,6,7] "identity/locator/declaration"
  let oldAxioms ← readOld "registry/axioms.tsv"
  if (tableFromText oldAxioms).records[0]?.getD "" == (headers.find? (·.1 == "axioms")).get!.2 then
    let prior := index (records oldAxioms)
    require ((← rowsCurrent "registry/axioms.tsv").all fun row => match prior[col row 1]? with
      | none => true | some rowOld => oidAdvance (col rowOld 8) (col row 8)) "axiom type OID regressed; axiom type OID regression"
  else require ((tableFromText oldAxioms).records.size == 1) "base axioms.tsv carries rows under an unsupported schema"
  if !replay then compare "registry/claim-vocabulary-review.tsv" #[2,3] "vocabulary review"
  compare "registry/vocabulary.tsv" #[2,3,4,5,6,9,10] "declaration/module/kind/origin/parent/design/finiteness"
  compare "registry/modules.tsv" #[2,3] "source path/role"
  compare "registry/statement-modules.tsv" #[2,3] "statement source path/role"
  if modern then
    compare "registry/tracks.tsv" #[2,3,4] "track position/title/slug"
    compare "registry/sources.tsv" #[2,3,4,5,6,7,8,9,10,11,12,13,14] "source identity/position/bibliography"
    if !replay then compare "registry/source-invariants.tsv" #[2,3,4,5,6,7,8] "source frozen invariants"
    if before.files.contains "registry/source-items.tsv" then
      compare "registry/source-items.tsv" (if replay then #[2,3,4,5,6,7,9,10,11] else #[2,3,4,5,6,7,8,9,10,11])
        "source item identity/order/label"
      oldRows (← rowsOld "registry/item-claims.tsv") (← rowsCurrent "registry/item-claims.tsv") "registry/item-claims.tsv" "item-claim"
  else compare "references/tasaki-2020.tsv" #[2] "source identity"
  for (stem,label) in #[("dependencies","dependency"),("claim-axioms","claim-axiom"),
    ("claim-vocabulary","claim-vocabulary"),("imports","import"),("statement-imports","statement-import"),
    ("claim-context","claim-context")] do
    let path := "registry/" ++ stem ++ ".tsv"
    oldRows (← rowsOld path) (← rowsCurrent path) path label
  let vocabularyOld := index (← rowsOld "registry/vocabulary.tsv")
  for (column,diagnostic) in #[(7,"vocabulary type OID regressed; vocabulary type regression"),
    (8,"vocabulary declaration OID regressed; vocabulary declaration regression")] do
    require ((← rowsCurrent "registry/vocabulary.tsv").all fun row => match vocabularyOld[col row 1]? with
      | none => true | some prior => oidAdvance (col prior column) (col row column)) diagnostic
  let slicesOld ← rowsOld "registry/slices.tsv"
  let slicesCurrent ← rowsCurrent "registry/slices.tsv"
  let slicePositions : Std.HashMap (String × String) String := slicesOld.foldl
    (fun result row => result.insert (col row 1,col row 3) (col row 2)) {}
  for row in slicesCurrent do
    if let some position := slicePositions[(col row 1,col row 3)]? then
      require (col row 2 == position) "slice position changed; slice regression"
  for (key,_) in slicePositions do
    require (slicesCurrent.any fun row => (col row 1,col row 3) == key)
      "slice membership disappeared; slice regression"
  let oldPhase := (tableFromText (← readOld "registry/phase.tsv")).records[1]?.getD ""
  let newPhase := (tableFromText (← readCurrent "registry/phase.tsv")).records[1]?.getD ""
  require (phaseRank newPhase ≥ phaseRank oldPhase) s!"phase regression: {oldPhase} -> {newPhase}"
  let oldPages := index (← rowsOld "registry/pages.tsv")
  require ((← rowsCurrent "registry/pages.tsv").all fun row => match oldPages[col row 1]? with
    | none => true
    | some prior => (col prior 10 == "PENDING" || col row 10 == col prior 10) &&
      passRank (col row 8) ≥ passRank (col prior 8) && passRank (col row 9) ≥ passRank (col prior 9))
    "page OID or census pass regressed; page state regression"
  let claimsOld := index (← rowsOld "registry/claims.tsv")
  let claimsCurrent := index (← rowsCurrent "registry/claims.tsv")
  let amendments := records (current.files["registry/claim-content-amendments.tsv"]?.getD "")
  let amendmentIndex : Std.HashMap String (String × String) := amendments.foldl (fun result row =>
    if replay && col row 2 == event then result.insert (col row 4) (col row 5,col row 6) else result) {}
  for row in ← rowsCurrent "registry/claims.tsv" do
    if let some prior := claimsOld[col row 1]? then
      let amended := amendmentIndex[col row 1]? == some (col prior 9,col row 9)
      require ((if col prior 9 == "PENDING" then col row 9 == "PENDING" || oid (col row 9)
        else oid (col prior 9) && (col row 9 == col prior 9 || amended)) &&
        (col prior 12 != "true" || col row 12 == "true"))
        "claim OID or tombstone regressed; claim state regression"
  if allowSupersession && !replay then
    for (id,prior) in claimsOld do
      let row := claimsCurrent[id]?.getD #[]
      let unchanged := projection prior #[12,13,14,15] == projection row #[12,13,14,15]
      let advanced := col prior 9 == col row 9 && projection prior #[12,13,14,15] == #["false","NONE","NONE","NONE"] &&
        col row 12 == "true" && col row 13 != "NONE" && col row 13 != id &&
        col row 14 != "NONE" && token (col row 14) && col row 15 != "NONE" && token (col row 15) &&
        claimsCurrent.contains (col row 13) && !claimsOld.contains (col row 13)
      require (unchanged || advanced) "invalid dedicated supersession transition; supersession transition regression"
  for stem in #["correction-events","claim-normalization-reviews","claim-corrections",
    "claim-successors","source-item-additions","claim-content-amendments","claim-location-amendments"] do
    let path := "registry/" ++ stem ++ ".tsv"
    if before.files.contains path then
      let text ← readCurrent path
      unless replay do require (text == (← readOld path)) s!"{path} historical correction ledger drift"
    else if (stem == "claim-content-amendments" || stem == "claim-location-amendments") && !replay && current.files.contains path then
      require ((← readCurrent path) == (← readOld path))
        (if stem == "claim-location-amendments" then "unowned location amendment ledger addition" else "unowned content amendment ledger addition")
  let oldBindingsText ← readOld "registry/bindings.tsv"
  unless (tableFromText oldBindingsText).records[0]?.getD "" == (headers.find? (·.1 == "bindings")).get!.2 do
    require ((tableFromText oldBindingsText).records.size == 1) "base bindings.tsv carries rows under an unsupported schema"
  let bindingOld := index (records oldBindingsText)
  let bindingRows ← rowsCurrent "registry/bindings.tsv"
  for (id,_) in bindingOld do
    require (bindingRows.any (col · 1 == id)) "binding disappeared or identity drifted; binding regression"
  for after in bindingRows do
    let some row := bindingOld[col after 1]? | continue
    require (projection row #[2,4] == projection after #[2,4]) "binding disappeared or identity drifted; binding regression"
    for column in #[3,5,6,7,8,9,10,11,13,14] do
      let value := col row column
      require (value.isEmpty || value == "NONE" || value == "PENDING" || value == col after column)
        "binding disappeared or identity drifted; binding regression"
    require (oneOf (col row 12) "|NONE|PENDING" || (!oneOf (col after 12) "|NONE"))
      "proof value regressed to an unresolved hole; binding regression"
  let sourcePath := if modern then "registry/sources.tsv" else "references/tasaki-2020.tsv"
  let sourceOld := index (← rowsOld sourcePath)
  for row in ← rowsCurrent sourcePath do
    if let some prior := sourceOld[col row 1]? then
      let pc := if modern then 15 else 4
      let tc := pc + 1
      let cc := pc + 2
      let oldPDF := col prior pc; let oldText := col prior tc
      let currentPDF := col row pc; let currentText := col row tc
      let initial := (currentPDF.isEmpty && currentText.isEmpty) ||
        (oid currentPDF && oid currentText && currentPDF.length == currentText.length)
      let frozen := if oldPDF.isEmpty && oldText.isEmpty then initial else
        currentPDF == oldPDF && currentText == oldText && (modern ||
          (oid oldPDF && oid oldText && oldPDF.length == oldText.length))
      let validCoverage := coverageRank (col row cc) ≥ coverageRank (col prior cc) &&
        (modern || (coverageRank (col row cc) > 0 && coverageRank (col prior cc) > 0))
      require (frozen && validCoverage) (if modern then "source fingerprint or coverage regression" else
        "reference fingerprint or coverage regressed; reference regression")
      unless modern do
        let edition := col prior 3; let currentEdition := col row 3
        let validEdition := fun value : String => !value.isEmpty &&
          alnum value.toList.head! && value.toList.all (fun c => alnum c || "._+-".contains c) &&
          !oneOf value.toLower "unspecified|pending|unknown|none"
        require (if edition == "unspecified" then currentEdition == edition || validEdition currentEdition
          else validEdition edition && currentEdition == edition) "reference fingerprint or coverage regressed; reference regression"
  if modern then
    let progressOld := index (← rowsOld "registry/source-progress.tsv")
    for row in ← rowsCurrent "registry/source-progress.tsv" do
      require (match progressOld[col row 1]? with
        | none => col row 2 == "registered"
        | some prior => lifecycleRank (col row 2) ≥ lifecycleRank (col prior 2))
        "source lifecycle regression or non-registered source addition"
    let oldTracks ← rowsOld "registry/tracks.tsv"
    let trackFront := oldTracks.foldl (fun n row => max n ((col row 2).toNat?.getD 0)) 0
    let oldTrackIds := index oldTracks
    require ((← rowsCurrent "registry/tracks.tsv").all fun row => oldTrackIds.contains (col row 1) ||
      (col row 2).toNat?.getD 0 > trackFront) "new track inserted before frozen track frontier"
    for row in ← rowsCurrent "registry/sources.tsv" do
      unless sourceOld.contains (col row 1) do
        let frontier := (← rowsOld "registry/sources.tsv").foldl (fun n prior =>
          if col prior 2 == col row 2 then max n ((col prior 3).toNat?.getD 0) else n) 0
        require ((col row 3).toNat?.getD 0 > frontier) "new source inserted before frozen source frontier"

end Checker.BaseDiff
