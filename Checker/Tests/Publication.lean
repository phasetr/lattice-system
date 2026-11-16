import Checker.Publication.Render

/-! The four original publication tests retain their synthetic inputs and public/private oracles. -/
namespace Checker.Tests.Publication
open Lean System Checker.CheckAll Checker.Publication

/-- Synthetic input from the original groupingInput test. -/
def groupingInput : String := "{\"tracks\":[{\"track_id\":\"TR-SRC\",\"position\":\"1\",\"title\":\"Test track\",\"public_slug\":\"test\"}],\"sources\":[{\"source_id\":\"SRC\",\"track_id\":\"TR-SRC\",\"source_position\":\"1\",\"source_kind\":\"book\",\"citation_key\":\"SRC\",\"title\":\"Safe title\",\"authors\":\"Safe author\",\"year\":\"2020\",\"edition\":\"safe-edition\",\"identifier_kind\":\"doi\",\"identifier\":\"10.example/test\",\"public_url\":\"https://example.test\",\"public_slug\":\"source\",\"local_ref_key\":\"PRIVATE-PATH\",\"pdf_oid\":\"PRIVATE-PDF-OID\",\"text_oid\":\"PRIVATE-TEXT-OID\",\"coverage\":\"frozen\"}],\"source_progress\":[{\"source_id\":\"SRC\",\"lifecycle\":\"vocabulary_reviewed\",\"review_ref\":\"REVIEW\"}],\"pages\":[{\"page_id\":\"PG-SRC-0001\",\"source_id\":\"SRC\",\"order_key\":\"000001\",\"printed_page\":\"1\",\"pdf_page\":\"1\",\"section\":\"§1.1\",\"page_kind\":\"body\",\"pass1\":\"complete\",\"pass2\":\"complete\",\"source_oid\":\"PRIVATE-PAGE-OID\"}],\"claims\":[{\"source_id\":\"SRC\",\"page_id\":\"PG-SRC-0001\",\"disposition\":\"assertion\",\"subkind\":\"theorem\",\"normalized_content\":\"PRIVATE SOURCE TEXT\",\"content_oid\":\"PRIVATE-CONTENT-OID\",\"exclusion_rationale\":\"NONE\",\"exclusion_review_ref\":\"NONE\",\"tombstone\":\"false\",\"superseded_by\":\"NONE\",\"tombstone_rationale\":\"NONE\",\"tombstone_review_ref\":\"NONE\",\"claim_id\":\"CL-SRC-0001\",\"order_key\":\"000001.0001\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1; atom 1\"},{\"source_id\":\"SRC\",\"page_id\":\"PG-SRC-0001\",\"disposition\":\"assertion\",\"subkind\":\"theorem\",\"normalized_content\":\"PRIVATE SOURCE TEXT\",\"content_oid\":\"PRIVATE-CONTENT-OID\",\"exclusion_rationale\":\"NONE\",\"exclusion_review_ref\":\"NONE\",\"tombstone\":\"false\",\"superseded_by\":\"NONE\",\"tombstone_rationale\":\"NONE\",\"tombstone_review_ref\":\"NONE\",\"claim_id\":\"CL-SRC-0002\",\"order_key\":\"000001.0002\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1; atom 2\"},{\"source_id\":\"SRC\",\"page_id\":\"PG-SRC-0001\",\"disposition\":\"assertion\",\"subkind\":\"theorem\",\"normalized_content\":\"PRIVATE SOURCE TEXT\",\"content_oid\":\"PRIVATE-CONTENT-OID\",\"exclusion_rationale\":\"NONE\",\"exclusion_review_ref\":\"NONE\",\"tombstone\":\"false\",\"superseded_by\":\"NONE\",\"tombstone_rationale\":\"NONE\",\"tombstone_review_ref\":\"NONE\",\"claim_id\":\"CL-SRC-0003\",\"order_key\":\"000001.0003\",\"locator\":\"PDF p. 1; §1.1; paragraph 2\"}],\"source_items\":[{\"item_id\":\"IT-SRC-0001\",\"source_id\":\"SRC\",\"order_key\":\"000001.0001\",\"page_id\":\"PG-SRC-0001\",\"item_kind\":\"theorem\",\"source_label\":\"Theorem 1.1\",\"title\":\"NONE\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1\",\"public_group\":\"Chapter 01\",\"public_slug\":\"chapter-01\",\"review_ref\":\"PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1\"},{\"item_id\":\"IT-SRC-0002\",\"source_id\":\"SRC\",\"order_key\":\"000001.0003\",\"page_id\":\"PG-SRC-0001\",\"item_kind\":\"unlabeled\",\"source_label\":\"NONE\",\"title\":\"NONE\",\"locator\":\"PDF p. 1; §1.1; paragraph 2\",\"public_group\":\"Chapter 01\",\"public_slug\":\"chapter-01\",\"review_ref\":\"PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1\"}],\"item_claims\":[{\"item_id\":\"IT-SRC-0001\",\"position\":\"1\",\"claim_id\":\"CL-SRC-0001\"},{\"item_id\":\"IT-SRC-0001\",\"position\":\"2\",\"claim_id\":\"CL-SRC-0002\"},{\"item_id\":\"IT-SRC-0002\",\"position\":\"1\",\"claim_id\":\"CL-SRC-0003\"}],\"claim_vocabulary_review\":[{\"claim_id\":\"CL-SRC-0001\",\"basis\":\"mathlib_only\",\"review_ref\":\"REVIEW\"},{\"claim_id\":\"CL-SRC-0002\",\"basis\":\"mathlib_only\",\"review_ref\":\"REVIEW\"},{\"claim_id\":\"CL-SRC-0003\",\"basis\":\"mathlib_only\",\"review_ref\":\"REVIEW\"}],\"vocabulary\":[],\"claim_vocabulary\":[],\"bindings\":[],\"axioms\":[],\"claim_axioms\":[],\"phase\":[{\"phase\":\"vocabulary\"}]}"

/-- Synthetic input from the original twoSourcesInput test. -/
def twoSourcesInput : String := "{\"tracks\":[{\"track_id\":\"TR-FIRST\",\"position\":\"1\",\"title\":\"First\",\"public_slug\":\"first-track\"},{\"track_id\":\"TR-SECOND\",\"position\":\"2\",\"title\":\"Second\",\"public_slug\":\"second-track\"}],\"sources\":[{\"source_kind\":\"paper\",\"authors\":\"Author\",\"year\":\"2026\",\"edition\":\"v1\",\"identifier_kind\":\"none\",\"identifier\":\"NONE\",\"public_url\":\"NONE\",\"local_ref_key\":\"PRIVATE\",\"pdf_oid\":\"PRIVATE\",\"text_oid\":\"PRIVATE\",\"coverage\":\"frozen\",\"source_id\":\"ZFIRST\",\"track_id\":\"TR-FIRST\",\"source_position\":\"1\",\"citation_key\":\"FIRST\",\"title\":\"First source\",\"public_slug\":\"first-source\"},{\"source_kind\":\"paper\",\"authors\":\"Author\",\"year\":\"2026\",\"edition\":\"v1\",\"identifier_kind\":\"none\",\"identifier\":\"NONE\",\"public_url\":\"NONE\",\"local_ref_key\":\"PRIVATE\",\"pdf_oid\":\"PRIVATE\",\"text_oid\":\"PRIVATE\",\"coverage\":\"frozen\",\"source_id\":\"ASECOND\",\"track_id\":\"TR-SECOND\",\"source_position\":\"1\",\"citation_key\":\"SECOND\",\"title\":\"Second source\",\"public_slug\":\"second-source\"}],\"pages\":[{\"page_id\":\"PG-ZFIRST-0001\",\"source_id\":\"ZFIRST\",\"order_key\":\"000001\",\"printed_page\":\"1\",\"pdf_page\":\"1\",\"section\":\"§1.1\",\"page_kind\":\"content\",\"pass1\":\"complete\",\"pass2\":\"complete\",\"source_oid\":\"PRIVATE\"},{\"page_id\":\"PG-ASECOND-0001\",\"source_id\":\"ASECOND\",\"order_key\":\"000001\",\"printed_page\":\"1\",\"pdf_page\":\"1\",\"section\":\"§1.1\",\"page_kind\":\"content\",\"pass1\":\"complete\",\"pass2\":\"complete\",\"source_oid\":\"PRIVATE\"}],\"claims\":[{\"disposition\":\"assertion\",\"subkind\":\"theorem\",\"normalized_content\":\"PRIVATE\",\"content_oid\":\"PRIVATE\",\"exclusion_rationale\":\"NONE\",\"exclusion_review_ref\":\"NONE\",\"tombstone\":\"false\",\"superseded_by\":\"NONE\",\"tombstone_rationale\":\"NONE\",\"tombstone_review_ref\":\"NONE\",\"claim_id\":\"CL-ASECOND-0001\",\"source_id\":\"ASECOND\",\"order_key\":\"000001.0001\",\"page_id\":\"PG-ASECOND-0001\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1\"},{\"disposition\":\"assertion\",\"subkind\":\"theorem\",\"normalized_content\":\"PRIVATE\",\"content_oid\":\"PRIVATE\",\"exclusion_rationale\":\"NONE\",\"exclusion_review_ref\":\"NONE\",\"tombstone\":\"false\",\"superseded_by\":\"NONE\",\"tombstone_rationale\":\"NONE\",\"tombstone_review_ref\":\"NONE\",\"claim_id\":\"CL-ZFIRST-0001\",\"source_id\":\"ZFIRST\",\"order_key\":\"000001.0001\",\"page_id\":\"PG-ZFIRST-0001\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1\"}],\"source_items\":[{\"item_id\":\"IT-ZFIRST-0001\",\"source_id\":\"ZFIRST\",\"order_key\":\"000001.0001\",\"page_id\":\"PG-ZFIRST-0001\",\"item_kind\":\"theorem\",\"source_label\":\"Theorem 1.1\",\"title\":\"NONE\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1\",\"public_group\":\"Chapter 01\",\"public_slug\":\"chapter-01\",\"review_ref\":\"PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1\"},{\"item_id\":\"IT-ASECOND-0001\",\"source_id\":\"ASECOND\",\"order_key\":\"000001.0001\",\"page_id\":\"PG-ASECOND-0001\",\"item_kind\":\"theorem\",\"source_label\":\"Theorem 1.1\",\"title\":\"NONE\",\"locator\":\"PDF p. 1; §1.1; Theorem 1.1\",\"public_group\":\"Chapter 01\",\"public_slug\":\"chapter-01\",\"review_ref\":\"PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1\"}],\"item_claims\":[{\"item_id\":\"IT-ZFIRST-0001\",\"position\":\"1\",\"claim_id\":\"CL-ZFIRST-0001\"},{\"item_id\":\"IT-ASECOND-0001\",\"position\":\"1\",\"claim_id\":\"CL-ASECOND-0001\"}],\"source_progress\":[{\"source_id\":\"ZFIRST\",\"lifecycle\":\"vocabulary_reviewed\",\"review_ref\":\"R\"},{\"source_id\":\"ASECOND\",\"lifecycle\":\"registered\",\"review_ref\":\"R\"}],\"claim_vocabulary_review\":[{\"claim_id\":\"CL-ASECOND-0001\",\"basis\":\"project_vocabulary\",\"review_ref\":\"R\"},{\"claim_id\":\"CL-ZFIRST-0001\",\"basis\":\"project_vocabulary\",\"review_ref\":\"R\"}],\"vocabulary\":[{\"vocabulary_id\":\"VO-LS-0001\",\"declaration\":\"Fixture.FirstTerm\",\"module\":\"Fixture.First\",\"declaration_kind\":\"definition\",\"origin\":\"primary\",\"parent_vocabulary_id\":\"NONE\",\"type_oid\":\"PRIVATE\",\"declaration_oid\":\"PRIVATE\",\"design_role\":\"fixture\",\"finiteness_scope\":\"none\"},{\"vocabulary_id\":\"VO-LS-0002\",\"declaration\":\"Fixture.SecondTerm\",\"module\":\"Fixture.Second\",\"declaration_kind\":\"definition\",\"origin\":\"primary\",\"parent_vocabulary_id\":\"NONE\",\"type_oid\":\"PRIVATE\",\"declaration_oid\":\"PRIVATE\",\"design_role\":\"fixture\",\"finiteness_scope\":\"none\"}],\"claim_vocabulary\":[{\"claim_id\":\"CL-ZFIRST-0001\",\"vocabulary_id\":\"VO-LS-0001\"},{\"claim_id\":\"CL-ASECOND-0001\",\"vocabulary_id\":\"VO-LS-0002\"}],\"axioms\":[],\"claim_axioms\":[],\"bindings\":[{\"claim_id\":\"CL-ZFIRST-0001\",\"statement_decl\":\"Fixture.statement\",\"proof_decl\":\"Fixture.proof\",\"module\":\"Fixture.Module\",\"statement_kind\":\"definition\",\"statement_shape\":\"proof_proposition\",\"statement_type_oid\":\"PRIVATE\",\"statement_value_oid\":\"PRIVATE\",\"implementation_status\":\"proof_stub\",\"proof_kind\":\"theorem\",\"proof_type_oid\":\"PRIVATE\",\"proof_value_oid\":\"NONE\",\"nonvacuity_decl\":\"NONE\",\"nonvacuity_oid\":\"NONE\",\"review_ref\":\"FIXTURE-REVIEW\"}],\"phase\":[{\"phase\":\"vocabulary\"}]}"

/-- Materialize only the original synthetic in-memory table collection. -/
def fixture (text : String) : IO Data := do
  let value ← parse text
  let tables ← (keys value).foldlM (fun tables name => do pure (tables.insert name (← arr value name)))
    ({} : Std.HashMap String (Array Row))
  return ⟨".",tables⟩

/-- Test assertions are mandatory executable checks, independent of optimization flags. -/
def check (condition : Bool) (message : String) : IO Unit := require condition ("publication test: " ++ message)

/-- Numeric chapter paths follow source order rather than unpadded lexical numerals. -/
def chapterPaths : IO Unit := do
  let (groups,paths) ← #[1,2,9,10,11].foldlM (fun (groups,paths) n => do
    let group ← publicGroup (stringRow #[("section",s!"§{n}.1"),("page_kind","body")]) s!"PDF p. {n}; §{n}.1"
    pure (groups.push group, paths.push ("docs/generated/groups/source/" ++ (← slugForGroup group) ++ ".md")))
    ((#[],#[]) : Array String × Array String)
  check (groups == #["Chapter 01","Chapter 02","Chapter 09","Chapter 10","Chapter 11"]) "numeric chapter display"
  check (paths == paths.qsort (· < ·)) "numeric chapter lexical order"
  check ((← slugForGroup "Chapter 1") == "chapter-01") "chapter slug padding"
  check ((← slugForGroup "Appendix A") == "appendix-a") "appendix slug"
  check ((← slugForGroup "Front matter") == "front-matter") "front matter slug"

/-- Label grouping and derivation retain atomic relations while excluding every original private sentinel. -/
def groupingPrivacy : IO Unit := do
  let data ← fixture groupingInput
  let (items,relations) ← derive (← data.rows "claims") (← data.rows "pages") (← data.rows "sources") (← data.rows "tracks")
  check (items.size == 2 && (← str items[0]! "source_label") == "Theorem 1.1") "named source-item grouping"
  check ((← (relations.extract 0 2).mapM (fun row => str row "position")) == #["1","2"]) "atomic relation order"
  check ((← str items[1]! "source_label") == "NONE") "unlabeled source item"
  let data := {data with tables := (data.tables.insert "source_items" items).insert "item_claims" relations}
  let outputs ← buildOutputs (← publicCatalog data)
  let combined := String.join ((outputs.toArray.map Prod.snd).toList)
  for privateText in #["PRIVATE SOURCE TEXT","PRIVATE-CONTENT-OID","PRIVATE-PATH","PRIVATE-PDF-OID","PRIVATE-TEXT-OID","normalized_content"] do
    check ((combined.splitOn privateText).length == 1) "private data excluded from every public output"

/-- Two-source ordering, lifecycle qualification, binding display and per-track vocabulary remain independent. -/
def twoSources : IO Unit := do
  let data ← fixture twoSourcesInput
  let (items,relations) ← derive (← data.rows "claims") (← data.rows "pages") (← data.rows "sources") (← data.rows "tracks")
  check ((← items.mapM (fun row => str row "source_id")) == #["ZFIRST","ASECOND"]) "track/source order precedes lexical source IDs"
  let data := {data with tables := (data.tables.insert "source_items" items).insert "item_claims" relations}
  let catalog ← publicCatalog data
  check ((← nat catalog "schema_version") == 2) "catalog schema"
  let catalogItems ← arr catalog "items"
  check ((← str catalogItems[0]! "source_id") == "ZFIRST") "public item order"
  let statuses ← catalogItems.foldlM (fun statuses item => do
    (← arr item "claims").foldlM (fun statuses claim => do
      pure (statuses.insert (← str claim "claim_id") (← str claim "vocabulary_status"))) statuses)
    ({} : Std.HashMap String String)
  check (statuses["CL-ZFIRST-0001"]? == some "vocabulary_ready") "reviewed source readiness"
  check (statuses["CL-ASECOND-0001"]? == some "review_staged") "registered source is not yet ready"
  let outputs ← buildOutputs catalog
  let firstPath := "docs/generated/groups/first-source/chapter-01.md"
  let secondPath := "docs/generated/groups/second-source/chapter-01.md"
  check (outputs.contains firstPath && outputs.contains secondPath) "source-scoped public groups"
  let first := outputs[firstPath]?.getD ""
  for text in #["CL-ZFIRST-0001","Fixture.statement","Fixture.Module","Fixture.proof"] do
    check ((first.splitOn text).length > 1) "registered first-source display"
  check ((first.splitOn "CL-ASECOND-0001").length == 1) "source groups do not mix"
  for slug in #["first-source","second-source"] do
    check (((outputs["docs/generated/sources/" ++ slug ++ ".md"]?.getD "").splitOn "Registered source items: 1").length > 1) "per-source item count"
  let firstTrack := outputs["docs/generated/tracks/first-track.md"]?.getD ""
  let secondTrack := outputs["docs/generated/tracks/second-track.md"]?.getD ""
  for text in #[firstTrack,secondTrack] do check ((text.splitOn "Active claims: 1").length > 1) "per-track active count"
  check ((firstTrack.splitOn "Fixture.FirstTerm").length > 1 && (firstTrack.splitOn "Fixture.SecondTerm").length == 1) "first-track vocabulary"
  check ((secondTrack.splitOn "Fixture.SecondTerm").length > 1 && (secondTrack.splitOn "Fixture.FirstTerm").length == 1) "second-track vocabulary"
  let source := outputs["docs/generated/sources/first-source.md"]?.getD ""
  check ((source.splitOn "Public reference: `NONE`").length > 1 && (source.splitOn "[NONE](NONE)").length == 1) "missing public reference is not a link"
  check ((source.splitOn "Census coverage label: `frozen`").length > 1 &&
    (source.splitOn "Source lifecycle: `vocabulary_reviewed`").length > 1)
    "coverage and source lifecycle have distinct display labels"

/-- Write/check behavior is exercised only under an automatically retired external directory. -/
def writeCheck : IO Unit := IO.FS.withTempDir fun root => do
  let outputs := ({} : Std.HashMap String String).insert "docs/index.md" "# Public\n" |>.insert "docs/generated/index.md" "# Generated\n" |>.insert "docs/generated/catalog.json" "{\"safe\": true}\n"
  writeOutputs root outputs
  check (← checkOutputs root outputs true) "fresh generated files match"
  IO.FS.writeFile (root / "docs/generated/index.md") "drift\n"
  check (!(← checkOutputs root outputs true)) "outdated generated file is rejected"
  IO.FS.withTempDir fun owner => do
    let target := owner / "target"; let outside := owner / "outside"
    IO.FS.createDir target; IO.FS.createDir outside
    let link ← IO.Process.output {cmd := "ln", args := #["-s",outside.toString,(target / "docs").toString]}
    check (link.exitCode == 0) "create output ancestor counterfactual"
    let rejected ← try writeOutputs target outputs; pure false catch _ => pure true
    check rejected "symbolic docs ancestor is rejected before creating directories"
    check (!(← (outside / "generated").pathExists)) "external directory remains absent"
  IO.FS.withTempDir fun owner => do
    IO.FS.createDir (owner / "docs")
    let outside := owner / "uncreated"
    let link ← IO.Process.output {cmd := "ln", args := #["-s",outside.toString,(owner / "docs/index.md").toString]}
    check (link.exitCode == 0) "create dangling output counterfactual"
    let rejected ← try writeOutputs owner outputs; pure false catch _ => pure true
    check rejected "dangling expected output is rejected"
    check (!(← outside.pathExists)) "dangling target remains absent"
  IO.FS.withTempDir fun owner => do
    let target := owner / "target"
    let outside := owner / "shared.md"
    IO.FS.createDirAll (target / "docs")
    IO.FS.writeFile outside "shared sentinel\n"
    IO.FS.hardLink outside (target / "docs/index.md")
    writeOutputs target outputs
    check ((← IO.FS.readFile outside) == "shared sentinel\n") "shared output inode remains unchanged"
    check (← checkOutputs target outputs true) "hard-linked output is replaced with generated bytes"

/-- Run precisely the four original publication test contracts. -/
def run : IO Unit := do
  chapterPaths; groupingPrivacy; twoSources; writeCheck
  IO.println "generate-public-docs tests: 4 passed"

end Checker.Tests.Publication
