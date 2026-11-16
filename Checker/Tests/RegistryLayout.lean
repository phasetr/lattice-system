import Checker.RegistryLayout

/-! Independent source-view controls for compact and literal historical registry layouts. -/
namespace Checker.Tests.RegistryLayout
open Checker.CheckAll Checker.RegistryLayout

private abbrev Row := Array String

private def path (stem : String) : String := "registry/" ++ stem ++ ".tsv"

private def identityHeader : Row := #["source_id", "track_id", "source_position", "source_kind",
  "citation_key", "title", "authors", "year", "edition", "identifier_kind", "identifier", "public_url",
  "public_slug", "local_ref_key", "pdf_oid", "text_oid"]

private def compactHeader : Row := identityHeader ++ #["lifecycle", "lifecycle_review_ref",
  "physical_page_count", "census_oid", "census_review_ref"]

private def logicalHeader : Row := identityHeader.push "coverage"

private def itemHeader : Row := #["item_id", "source_id", "order_key", "page_id", "item_kind",
  "source_label", "title", "locator", "public_group", "public_slug"]

private def oid : String := "1111111111111111111111111111111111111111"

private def identity : Row := #["SOURCE", "TR-TEST", "1", "book", "TEST", "Synthetic source",
  "Test Author", "2026", "test-edition", "none", "NONE", "NONE", "test", "synthetic.pdf", oid, oid]

private def mappings : Array (String × String) := #[
  ("registered", "pending"), ("source_frozen", "pending"), ("census_pass1", "pass1"),
  ("census_pass2", "pass2"), ("census_reconciled", "reconciled"), ("vocabulary_reviewed", "frozen"),
  ("skeleton_frozen", "frozen"), ("proof_active", "frozen"), ("complete", "frozen")]

private def reconciled (stage : String) : Bool :=
  #["census_reconciled", "vocabulary_reviewed", "skeleton_frozen", "proof_active", "complete"].contains stage

private def compactRow (stage : String := "vocabulary_reviewed") : Row :=
  let identity := if stage == "registered" then (identity.set! 14 "").set! 15 "" else identity
  identity ++ #[stage, "LIFECYCLE-REVIEW"] ++
    (if reconciled stage then #["99", oid, "CENSUS-REVIEW"] else #["NONE", "NONE", "NONE"])

private def itemRow : Row := #["IT-SOURCE-0001", "SOURCE", "000001.0001", "PG-SOURCE-0001",
  "unlabeled", "NONE", "Synthetic item", "PDF p. 1; print p. 1; §1; paragraph 1", "Chapter 01", "chapter-01"]

private def pageHeader : Row := #["page_id", "source_id", "order_key", "printed_page", "pdf_page",
  "section", "page_kind", "pass1", "pass2", "source_oid"]

private def claimHeader : Row := #["claim_id", "source_id", "order_key", "page_id", "locator",
  "disposition", "subkind", "normalized_content", "content_oid", "exclusion_rationale",
  "exclusion_review_ref", "tombstone", "superseded_by", "tombstone_rationale", "tombstone_review_ref"]

private def pages : Array Row := #["0001", "0002", "0003"].map fun suffix =>
  #["PG-SOURCE-" ++ suffix, "SOURCE", "00" ++ suffix, "1", "1", "§1", "body", "complete", "complete", oid]

private def claim (suffix page disposition kind tombstone : String) : Row :=
  #["CL-SOURCE-" ++ suffix, "SOURCE", "000001." ++ suffix, "PG-SOURCE-" ++ page,
    "synthetic location", disposition, kind, "Synthetic assertion", oid, "NONE", "NONE",
    tombstone, "NONE", "NONE", "NONE"]

/-- Excluded active equations still use pages; tombstones and another source do not. -/
private def claims : Array Row := #[
  claim "0001" "0001" "assertion" "remark" "false",
  claim "0002" "0002" "out_of_scope" "equation" "false",
  claim "0003" "0003" "assertion" "equation" "true",
  (claim "0004" "0003" "assertion" "equation" "false").set! 1 "OTHER"]

private def text (header : Row) (rows : Array Row) : String :=
  String.intercalate "\t" header.toList ++ "\n" ++
    String.join (rows.toList.map fun row => String.intercalate "\t" row.toList ++ "\n")

private def compactFiles : Files :=
  ({} : Files).insert (path "sources") (text compactHeader #[compactRow])
    |>.insert (path "phase") "phase\nvocabulary\n"
    |>.insert (path "source-items") (text itemHeader #[itemRow])

private def withCorpus : Files := compactFiles.insert (path "pages") (text pageHeader pages)
  |>.insert (path "claims") (text claimHeader claims)

private def alteredSource (column : Nat) (value : String) : Files :=
  compactFiles.insert (path "sources") (text compactHeader #[(compactRow).set! column value])

private def tableRows (files : Files) (stem : String) : Array Row :=
  let lines := split (files[path stem]?.getD "") "\n"
  (lines.extract 1 (lines.size - 1)).map (split · "\t")

/-- Failure controls bind to the intended production diagnostic, never to any exception. -/
private def rejects (action : IO Unit) (diagnostic : String) : IO Unit := do
  let observed ← try action; pure (none : Option String) catch error => pure (some error.toString)
  require (observed.any fun message => (message.splitOn diagnostic).length > 1)
    ("expected registry-layout rejection: " ++ diagnostic)

private def normalizeCurrent (files : Files) : IO Unit := do
  discard <| normalize files .current

/-- Independent future schemas ensure that accidentally removing a registered table cannot pass. -/
private def futureSchemas : Array (String × Row) := #[
  ("slices", #["slice_id", "position", "claim_id"]),
  ("dependencies", #["claim_id", "role", "target_claim_id", "rationale"]),
  ("bindings", #["claim_id", "statement_decl", "proof_decl", "module", "statement_kind", "statement_shape",
    "statement_type_oid", "statement_value_oid", "implementation_status", "proof_kind", "proof_type_oid",
    "proof_value_oid", "nonvacuity_decl", "nonvacuity_oid", "review_ref"]),
  ("claim-context", #["claim_id", "position", "setup_claim_id", "use_kind", "scope", "review_ref"]),
  ("axioms", #["axiom_id", "declaration", "module", "category", "source_locator", "rationale", "reopen_condition", "axiom_type_oid"]),
  ("claim-axioms", #["claim_id", "axiom_id"]),
  ("statement-modules", #["module", "source_path", "role"]),
  ("statement-imports", #["module", "position", "imported_module", "is_exported", "is_meta", "import_all"])]

private def postR4Files (phase : String) : Files :=
  futureSchemas.foldl (fun files (stem, header) => files.insert (path stem) (text header #[]))
    (compactFiles.insert (path "phase") ("phase\n" ++ phase ++ "\n"))

private def mappingControl : IO Unit := do
  require (split sourceHeader "\t" == compactHeader && split legacySourceHeader "\t" == logicalHeader)
    "source schema order changed"
  for (stage, coverage) in mappings do
    let row := compactRow stage
    let projected ← projectSources compactHeader #[row] .current
    require (projected.compact && projected.header == logicalHeader &&
      projected.rows == #[(row.extract 0 16).push coverage] &&
      projected.progress == some #[#["SOURCE", stage, "LIFECYCLE-REVIEW"]] &&
      projected.anchors == some (if reconciled stage then #[#["SOURCE", "99", oid, "CENSUS-REVIEW"]] else #[]))
      ("wrong lifecycle projection: " ++ stage)

private def historicalControl : IO Unit := do
  let source := text logicalHeader #[identity.push "BROKEN-COVERAGE"]
  let badCounts := "unrecognized historical header\nSOURCE\t99\t-4\t999\n"
  let raw := ({} : Files).insert (path "sources") source
    |>.insert (path "source-invariants") badCounts
    |>.insert (path "source-items") (text (itemHeader.push "review_ref") #[itemRow.push "ORIGINAL-BAD-TAG"])
  for profile in #[Profile.historical, Profile.legacyFixture] do
    let view ← normalize raw profile
    require (!view.compact && view.files.size == raw.size &&
      raw.toArray.all (fun (key, value) => view.files[key]? == some value)) "historical bytes were repaired"
    let projected ← projectSources logicalHeader #[identity.push "BROKEN-COVERAGE"] profile
    require (projected.rows == #[identity.push "BROKEN-COVERAGE"] && projected.progress.isNone && projected.anchors.isNone)
      "historical coverage or missing state was inferred"

private def countsControl : IO Unit := do
  let view ← normalize withCorpus .current
  require (tableRows view.files "source-invariants" == #[#["SOURCE", "99", "2", "1", "1", "1", oid, "CENSUS-REVIEW"]])
    "census counters or independent anchors changed"
  require (view.files[path "pages"]? == withCorpus[path "pages"]? &&
    view.files[path "claims"]? == withCorpus[path "claims"]?) "census hash inputs changed"
  require (tableRows view.files "source-items" == #[itemRow.push "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"])
    "native item projection changed"

private def partialControl : IO Unit := do
  for raw in #[compactFiles, compactFiles.insert (path "pages") (text pageHeader pages),
      compactFiles.insert (path "claims") (text claimHeader claims)] do
    let view ← normalize raw .current
    require (!(view.files.contains (path "source-invariants"))) "partial corpus synthesized invariants"

private def quotedControl : IO Unit := do
  let quoted := "quoted\ttab\nand newline"
  let source := (compactRow).set! 5 quoted
  let projected ← projectSources compactHeader #[source] .current
  require (projected.rows[0]?.bind (·[5]?) == some quoted) "parsed source cell was split"
  let item := itemRow.set! 6 quoted
  let projected ← projectItems itemHeader #[item] true
  require (projected.header == itemHeader.push "review_ref" &&
    projected.rows == #[item.push "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"]) "parsed item cell or fixed tag changed"
  let row := #["CL-SOURCE-0001", "requires", "CL-SOURCE-0002", quoted]
  let projected ← projectFuture "proof" "dependencies" (some (#["claim_id", "role", "target_claim_id", "rationale"], #[row]))
  require (projected == #[row]) "parsed future cell was split"

private def preFutureControl : IO Unit := do
  require ((futureHeaders.map fun (stem, header) => (stem, split header "\t")) == futureSchemas)
    "future schema roster changed"
  let view ← normalize compactFiles .current
  for (stem, header) in futureSchemas do
    require (view.files[path stem]? == some (text header #[])) "absent pre-R4 future table was not projected"
    require ((← projectFuture "vocabulary" stem (some (header, #[]))).isEmpty) "observed empty future table changed"
  require (view.files[path "phase"]? == some "phase\nvocabulary\n") "global phase was inferred"

private def postFutureControl : IO Unit := do
  for (stem, header) in futureSchemas do
    let row := header.map (fun _ => "synthetic-field")
    require ((← projectFuture "proof" stem (some (header, #[row]))) == #[row]) "post-R4 parsed future rows changed"
  let view ← normalize (postR4Files "skeleton") .current
  require (view.compact) "complete post-R4 physical layout was rejected"

private def missingFutureControl : IO Unit := do
  for phase in #["skeleton", "proof"] do
    for (stem, _) in futureSchemas do
      rejects (normalizeCurrent ((postR4Files phase).erase (path stem)))
        ("missing " ++ stem ++ ".tsv in post-R4 compact registry")

private structure Control where
  label : String
  action : IO Unit

private def controls : Array Control := #[
  ⟨"registry-layout-nine-lifecycle-mappings", mappingControl⟩,
  ⟨"registry-layout-historical-literal-not-repaired", historicalControl⟩,
  ⟨"registry-layout-historical-missing-source", do
    for profile in #[Profile.historical, Profile.legacyFixture] do
      let raw := ({} : Files).insert "references/tasaki-2020.tsv" "literal R1 bytes"
      let view ← normalize raw profile
      require (!view.compact && view.files.toArray == raw.toArray) "R1 observation was replaced"⟩,
  ⟨"registry-layout-counters-and-independent-anchors", countsControl⟩,
  ⟨"registry-layout-partial-corpus", partialControl⟩,
  ⟨"registry-layout-quoted-parsed-cells", quotedControl⟩,
  ⟨"registry-layout-historical-item-tag", do
    let row := itemRow.push "ORIGINAL-BAD-TAG"
    let projected ← projectItems (itemHeader.push "review_ref") #[row] false
    require (projected.rows == #[row]) "historical item tag was repaired"⟩,
  ⟨"registry-layout-pre-r4-future-views", preFutureControl⟩,
  ⟨"registry-layout-post-r4-physical-future", postFutureControl⟩,
  ⟨"registry-layout-current-old-source-rejected", rejects
    (normalizeCurrent (compactFiles.insert (path "sources") (text logicalHeader #[identity.push "frozen"])))
    "current registry requires compact sources.tsv"⟩,
  ⟨"registry-layout-current-missing-source-rejected", rejects (normalizeCurrent (compactFiles.erase (path "sources")))
    "current registry requires compact sources.tsv"⟩,
  ⟨"registry-layout-draft-22-rejected", rejects
    (normalizeCurrent (compactFiles.insert (path "sources")
      (text (logicalHeader ++ compactHeader.extract 16 21) #[(identity.push "frozen") ++ (compactRow).extract 16 21])))
    "bad sources.tsv header for registry layout"⟩,
  ⟨"registry-layout-unknown-source-header", rejects
    (normalizeCurrent (compactFiles.insert (path "sources") (text (compactHeader.set! 0 "unknown_id") #[compactRow])))
    "bad sources.tsv header for registry layout"⟩,
  ⟨"registry-layout-source-row-width", rejects
    (normalizeCurrent (compactFiles.insert (path "sources") (text compactHeader #[(compactRow).pop])))
    "bad sources.tsv row width for registry layout"⟩,
  ⟨"registry-layout-old-progress-coexistence", rejects
    (normalizeCurrent (compactFiles.insert (path "source-progress") (progressHeader ++ "\n")))
    "compact sources cannot coexist with legacy source state tables"⟩,
  ⟨"registry-layout-old-invariant-coexistence", rejects
    (normalizeCurrent (compactFiles.insert (path "source-invariants") (invariantHeader ++ "\n")))
    "compact sources cannot coexist with legacy source state tables"⟩,
  ⟨"registry-layout-invalid-lifecycle", rejects (normalizeCurrent (alteredSource 16 "unknown")) "bad source lifecycle"⟩,
  ⟨"registry-layout-invalid-lifecycle-review", rejects (normalizeCurrent (alteredSource 17 "bad review")) "bad source progress review token"⟩,
  ⟨"registry-layout-partial-none-anchor", rejects (normalizeCurrent (alteredSource 20 "NONE")) "invalid compact source census anchors"⟩,
  ⟨"registry-layout-zero-physical-anchor", rejects (normalizeCurrent (alteredSource 18 "0")) "invalid compact source census anchors"⟩,
  ⟨"registry-layout-padded-physical-anchor", rejects (normalizeCurrent (alteredSource 18 "099")) "invalid compact source census anchors"⟩,
  ⟨"registry-layout-invalid-census-oid", rejects (normalizeCurrent (alteredSource 19 "PENDING")) "invalid compact source census anchors"⟩,
  ⟨"registry-layout-invalid-census-review", rejects (normalizeCurrent (alteredSource 20 "bad review")) "invalid compact source census anchors"⟩,
  ⟨"registry-layout-premature-anchor", rejects (normalizeCurrent (alteredSource 16 "census_pass2")) "reconciled source invariant membership mismatch"⟩,
  ⟨"registry-layout-missing-reconciled-anchor", rejects
    (normalizeCurrent (compactFiles.insert (path "sources")
      (text compactHeader #[((compactRow).extract 0 18) ++ #["NONE", "NONE", "NONE"]])))
    "reconciled source invariant membership mismatch"⟩,
  ⟨"registry-layout-missing-phase", rejects (normalizeCurrent (compactFiles.erase (path "phase"))) "compact registry requires phase.tsv"⟩,
  ⟨"registry-layout-unknown-phase", rejects
    (normalizeCurrent (compactFiles.insert (path "phase") "phase\nunknown\n")) "unknown phase for registry layout"⟩,
  ⟨"registry-layout-future-header", rejects
    (normalizeCurrent (compactFiles.insert (path "bindings") "unknown\n")) "bad bindings.tsv header for registry layout"⟩,
  ⟨"registry-layout-pre-r4-nonempty-future", rejects
    (normalizeCurrent (compactFiles.insert (path "slices") "slice_id\tposition\tclaim_id\nSL-TEST\t1\tCL-SOURCE-0001\n"))
    "pre-R4 compact registry requires header-only slices.tsv"⟩,
  ⟨"registry-layout-future-row-width", rejects
    (do discard <| projectFuture "proof" "slices" (some (#["slice_id", "position", "claim_id"], #[#["short"]])))
    "bad slices.tsv row width for registry layout"⟩,
  ⟨"registry-layout-each-post-r4-future-required", missingFutureControl⟩,
  ⟨"registry-layout-future-stem-boundary", do
    for stem in #["unknown", "registry/bindings.tsv"] do
      rejects (do discard <| projectFuture "vocabulary" stem none) "unknown future table for registry layout"⟩,
  ⟨"registry-layout-compact-old-item-rejected", rejects
    (normalizeCurrent (compactFiles.insert (path "source-items")
      (text (itemHeader.push "review_ref") #[itemRow.push "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"])))
    "bad source-items.tsv header for registry layout"⟩,
  ⟨"registry-layout-item-row-width", rejects
    (normalizeCurrent (compactFiles.insert (path "source-items") (text itemHeader #[itemRow.pop])))
    "bad source-items.tsv row width for registry layout"⟩,
  ⟨"registry-layout-item-header", rejects
    (do discard <| projectItems (itemHeader.set! 0 "unknown_id") #[itemRow] true)
    "bad source-items.tsv header for registry layout"⟩]

/-- Feed each independent control once into the existing self-test callback and counter. -/
def run (check : Bool → String → IO Unit) : IO Unit := do
  require (controls.size == 35 && (controls.map (·.label)).toList.eraseDups.length == controls.size)
    "registry-layout control roster changed"
  for control in controls do
    let success ← try control.action; pure true catch _ => pure false
    check success control.label

end Checker.Tests.RegistryLayout
