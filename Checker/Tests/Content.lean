import Checker.Tests.FixtureSupport

/-! Regression contracts for content amendments, omitted assertions and combined corrections. -/

namespace Checker.Tests.Content

open System Lean Checker.TestSupport Checker.Tests.FixtureSupport









/-- Insert a row before the first later source-order row. -/
def orderedInsert (rows : Array (Array String)) (row : Array String) : Array (Array String) := Id.run do
  let index := ((List.range rows.size).find? fun i => i > 0 &&
    rows[i]![1]! == row[1]! && rows[i]![2]! > row[2]!).getD rows.size
  return rows.extract 0 index ++ #[row] ++ rows.extract index rows.size




/-- Build a current-schema binding for deliberately ineligible source-state fixtures. -/
def bindingRow (root : FilePath) (id : String) : IO (Array String) := do
  let row ← record root "claims.tsv" id
  let proof := #["assertion", "conjecture"].contains row[5]!
  let shape := if proof then "proof_proposition" else
    if row[5]! == "definition" then "definition_value" else
    if row[5]! == "notation" then "notation_expansion" else
    if row[5]! == "hypothesis" then "hypothesis_prop" else "domain_type"
  pure #[id, "LatticeSystem.Claims.Runtime.statement",
    if proof then "LatticeSystem.Claims.Runtime.proof" else "NONE",
    "LatticeSystem.Claims.Runtime", "definition", shape, "PENDING", "PENDING",
    if proof then "proof_stub" else "definitional", if proof then "theorem" else "NONE",
    if proof then "PENDING" else "NONE", "NONE", "NONE", "NONE", "RUNTIME-BINDING-REVIEW"]

/-- Identities and original rows created by a same-assertion content repair. -/
structure Amendment where
  event : String
  review : String
  correction : String
  amendment : String
  old : Array String
  page : Array String

/-- Create the exact reviewed content-amendment fixture, including byte-based hashes. -/
def prepareAmendment (ctx : Context) (before after : FilePath) (content : String)
    (target : String := claim) : IO Amendment := do
  copyFixture ctx before after
  unless ← (after / "registry/claim-content-amendments.tsv").pathExists do
    writeTable after "claim-content-amendments.tsv" #[amendmentHeader]
  let event ← unusedId after "correction-events.tsv" "RUNTIME-CONTENT-EVENT"
  let review := event ++ "-REVIEW"
  let nr ← unusedId after "claim-normalization-reviews.tsv" "NR-RUNTIME"
  let cc ← unusedId after "claim-corrections.tsv" "CC-RUNTIME"
  let ca ← unusedId after "claim-content-amendments.tsv" "CA-RUNTIME"
  let old ← record before "claims.tsv" target
  let page ← record before "pages.tsv" old[3]!
  add after "correction-events.tsv" #[event, toString (← table after "correction-events.tsv").size,
    old[1]!, (← git ctx.project #["rev-parse", "HEAD"]).trimAscii.toString, review]
  add after "claim-normalization-reviews.tsv" #[nr, event, "1", target, "exact_statement_readiness",
    "amend_content", "closed", "restore-source-condition", review]
  add after "claim-corrections.tsv" #[cc, event, "1", nr, target, "amend_content",
    old[5]!, old[6]!, old[5]!, old[6]!]
  add after "claim-content-amendments.tsv" #[ca, event, cc, target, ← blob ctx old[7]!,
    ← blob ctx content, page[9]!, review]
  mutate after "claims.tsv" target 7 content
  mutate after "claims.tsv" target 8 (← blob ctx content)
  mutate after "claim-vocabulary-review.tsv" target 2 review
  refresh ctx after
  pure ⟨event, review, cc, ca, old, page⟩

/-- Identities created by an independently reviewed omission fixture. -/
structure Omission where
  event : String
  review : String
  normalization : String
  correction : String
  claim : String
  item : String

/-- Find the first unused nested order suffix, retaining the original sequential candidate search. -/
private partial def omissionSuffix (claims : Array (Array String)) (anchor : Array String) (suffix : Nat) : Nat :=
  if claims.any (fun r => r[1]?.getD "" == anchor[1]! && r[2]?.getD "" == anchor[2]! ++ "." ++ pad suffix) then
    omissionSuffix claims anchor (suffix+1)
  else suffix

/-- Create an omitted assertion either in a fresh item or in the original source item. -/
def prepareOmission (ctx : Context) (before after : FilePath) (newItem : Bool := true) : IO Omission := do
  copyFixture ctx before after
  let event ← unusedId after "correction-events.tsv" "RUNTIME-OMISSION-EVENT"
  let review := event ++ "-REVIEW"
  let nr ← unusedId after "claim-normalization-reviews.tsv" "NR-RUNTIME"
  let cc ← unusedId after "claim-corrections.tsv" "CC-RUNTIME"
  let id ← unusedId after "claims.tsv" "CL-TASAKI2020"
  let claims ← table after "claims.tsv"
  let anchor ← record after "claims.tsv" claim
  let content := "The two finite parity classes have equal cardinality."
  let suffix := omissionSuffix claims anchor 1
  let order := anchor[2]! ++ "." ++ pad suffix
  let locator := anchor[4]! ++ "; independently reviewed omitted assertion"
  let claims := orderedInsert claims #[id, anchor[1]!, order, anchor[3]!, locator, "assertion",
    "unnumbered_obligation", content, ← blob ctx content, "NONE", "NONE", "false", "NONE", "NONE", "NONE"]
  writeTable after "claims.tsv" claims
  add after "correction-events.tsv" #[event, toString (← table after "correction-events.tsv").size,
    anchor[1]!, (← git ctx.project #["rev-parse", "HEAD"]).trimAscii.toString, review]
  add after "claim-normalization-reviews.tsv" #[nr, event, "1", id, "exact_statement_readiness",
    "add_omitted_claim", "closed", "omitted-source-assertion", review]
  add after "claim-corrections.tsv" #[cc, event, "1", nr, id, "add_omitted_claim", "NONE", "NONE",
    "assertion", "unnumbered_obligation"]
  add after "claim-vocabulary-review.tsv" #[id, "mathlib_only", review]
  let relations ← table after "item-claims.tsv"
  let existing := (relations.find? fun r => r[2]?.getD "" == anchor[0]!).get!
  let (item,relations) ← if newItem then do
      let item ← unusedId after "source-items.tsv" "IT-TASAKI2020"
      let items ← table after "source-items.tsv"
      let sourceItem ← record after "source-items.tsv" existing[0]!
      writeTable after "source-items.tsv" <| orderedInsert items #[item, anchor[1]!, order,
        anchor[3]!, "unlabeled", "NONE", "NONE", locator, sourceItem[8]!, sourceItem[9]!, review]
      let ia ← unusedId after "source-item-additions.tsv" "IA-RUNTIME"
      add after "source-item-additions.tsv" #[ia, event, cc, "1", item, review]
      pure (item,insertAfter relations (· == existing) #[#[item, "1", id]])
    else do
      let item := existing[0]!
      let selected := relations.filter fun r => r[0]?.getD "" == item
      let position := 1 + (selected.foldl (fun n r => max n (r[1]!.toNat!)) 0)
      let last := ((List.range relations.size).filter fun i => relations[i]![0]! == item).getLast!
      let relations := relations.extract 0 (last + 1) ++ #[#[item, toString position, id]] ++
        relations.extract (last + 1) relations.size
      pure (item,relations)
  writeTable after "item-claims.tsv" relations
  mutate after "source-invariants.tsv" anchor[1]! 7 review
  refresh ctx after
  pure ⟨event, review, nr, cc, id, item⟩

/-- A pair of independently created omissions sharing one named source unit. -/
structure Grouped where
  first : Omission
  second : Omission

/-- Create canonical first-relation ownership for a two-member source item. -/
def prepareGrouped (ctx : Context) (before after : FilePath) : IO Grouped := do
  let firstPath := FilePath.mk (after.toString ++ "-first")
  let first ← prepareOmission ctx before firstPath
  let second ← prepareOmission ctx firstPath after
  remove after "correction-events.tsv" second.event
  for (name, id) in #[("claim-normalization-reviews.tsv", second.normalization),
      ("claim-corrections.tsv", second.correction)] do
    mutate after name id 1 first.event
    mutate after name id 2 "2"
  mutate after "claim-normalization-reviews.tsv" second.normalization 8 first.review
  mutate after "claim-vocabulary-review.tsv" second.claim 2 first.review
  remove after "source-items.tsv" second.item
  remove after "source-item-additions.tsv" second.item 4
  let relations := (← table after "item-claims.tsv").filter fun r => r[0]?.getD "" != second.item
  writeTable after "item-claims.tsv" <| insertAfter relations
    (fun r => r[0]?.getD "" == first.item) #[#[first.item, "2", second.claim]]
  let pageId := (← record after "claims.tsv" first.claim)[3]!
  let pageOrder := (← record after "pages.tsv" pageId)[2]!.toNat!
  let locator := s!"PDF p. {pageOrder}; Footnote 999"
  for (column, value) in #[(4, "footnote"), (5, "Footnote 999"), (7, locator),
      (10, "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1")] do mutate after "source-items.tsv" first.item column value
  for (position, id) in #[(1, first.claim), (2, second.claim)] do
    let content := s!"Synthetic private assertion {position} for a finite test family."
    mutate after "claims.tsv" id 4 (locator ++ s!"; assertion {position}")
    mutate after "claims.tsv" id 7 content
    mutate after "claims.tsv" id 8 (← blob ctx content)
  mutate after "source-invariants.tsv" "TASAKI2020" 7 first.review
  refresh ctx after
  pure ⟨first, second⟩

/-- Invoke the real correction transition route on two owned corpus trees. -/
def transition (ctx : Context) (label : String) (before after : FilePath)
    (positive : Bool := true) (diagnostic : String := "") : IO Unit := do
  discard <| expect ctx label positive
    (ctx.command "corrections" #["--fixture-dirs", before.toString, after.toString]) diagnostic

/-- Invoke the existing standalone content helper's static contract. -/
def static (ctx : Context) (label : String) (after : FilePath)
    (positive : Bool := true) (diagnostic : String := "") : IO Unit := do
  discard <| expect ctx label positive (ctx.content #["--static", after.toString]) diagnostic

/-- Invoke the actual ordinary or explicitly owned base-diff route. -/
def baseDiff (ctx : Context) (label : String) (before after : FilePath)
    (positive : Bool := true) (event : String := "") (diagnostic : String := "") : IO Unit := do
  let options := if event.isEmpty then #[] else #["--correction-event", event]
  discard <| expect ctx label positive (ctx.command "base-diff"
    (options ++ #["--fixture-dirs", before.toString, after.toString])) diagnostic

/-- Clone an owned corpus under a stable case name. -/
def caseCopy (ctx : Context) (name : String) (source : FilePath) : IO FilePath := do
  let target := ctx.temporary / name
  copyFixture ctx source target
  pure target








/-- Check grouping, member order and exclusion of private source bytes in the actual renderer. -/
def groupedPublic (ctx : Context) (base grouped : FilePath) (data : Grouped) : IO Unit := do
  generate ctx grouped
  let value ← catalog grouped
  let namedCount ← (← jsonArray (← property value "items")).foldlM (fun count item => do
    pure (if (← jsonString (← property item "item_id")) == data.first.item then count+1 else count)) 0
  ensure (namedCount == 1) "exactly one grouped public item"
  ensure ((← jsonArray (← property value "items")).size ==
    (← table base "source-items.tsv").size) "grouped catalog retains every source item"
  let named ← catalogItem value data.first.item
  ensure ((← jsonString (← property named "item_kind")) == "footnote" &&
    (← jsonString (← property named "source_label")) == "Footnote 999") "grouped item label"
  let ids ← (← jsonArray (← property named "claims")).mapM fun member => do jsonString (← property member "claim_id")
  ensure (ids == #[data.first.claim, data.second.claim]) "grouped public member order"
  let anchor ← record grouped "source-items.tsv" data.first.item
  ensure ((← jsonString (← property named "public_group")) == anchor[8]! &&
    (← jsonString (← property named "public_slug")) == anchor[9]!) "grouped public metadata"
  ensure ((← table grouped "source-items.tsv").size == (← table base "source-items.tsv").size + 1)
    "grouped item count"
  let text ← publicText (grouped / "docs")
  for id in #[data.first.claim, data.second.claim] do
    let row ← record grouped "claims.tsv" id
    for token in #[row[7]!, row[8]!] do ensure ((text.splitOn token).length == 1) "private grouped bytes"
  for token in #[data.first.review, "normalized_content"] do
    ensure ((text.splitOn token).length == 1) "private grouped metadata"
  generate ctx grouped "--check"

/-- Check historical empty-schema migration and both pending and frozen amendment bases. -/
def schemaHistoryCases (ctx : Context) (base current : FilePath) (am : Amendment)
    (omitted grouped : FilePath) : IO (FilePath × FilePath) := do
  let copy := caseCopy ctx
  let old := am.old
  let content := "For every admissible x, F(x) = G(x)."
  let oldSchema ← copy "empty-r4-schema-migration-base" base
  writeTable oldSchema "bindings.tsv" #[#["claim_id", "statement_decl", "proof_decl", "module", "statement_oid", "nonvacuity_decl"]]
  writeTable oldSchema "axioms.tsv" #[#["axiom_id", "declaration", "module", "category", "source_locator", "rationale", "reopen_condition"]]
  for name in #["claim-context.tsv", "statement-modules.tsv", "statement-imports.tsv"] do
    IO.FS.removeFile (oldSchema / "registry" / name)
  transition ctx "empty-r4-schema-migration" oldSchema current
  let adapterEmpty ← copy "adapter-historical-empty" oldSchema
  expectAction ctx "adapter-historical-empty" true (adaptEmpty ctx adapterEmpty)
  for name in artifactNames do
    ensure ((← table adapterEmpty name) == #[(← table ctx.project name)[0]!]) "adapter empty schemas"
  let adapterCurrent ← copy "adapter-current-populated" base
  let adapterRows := #[("bindings.tsv", ← bindingRow base claim),
    ("axioms.tsv", #["AX-PROJECT-9001", "LatticeSystem.Axioms.State.fixture", "LatticeSystem.Axioms.State", "state", "fixture", "fixture", "remove", "PENDING"]),
    ("claim-context.tsv", #["CL-TASAKI2020-0002", "1", claim, "term_reference", "inherited", "FIXTURE"]),
    ("statement-modules.tsv", #["LatticeSystem.Claims.Front", "LatticeSystem/Claims/Front.lean", "leaf"]),
    ("statement-imports.tsv", #["LatticeSystem.Claims.Front", "1", "Mathlib.Init", "true", "false", "false"])]
  let original ← adapterRows.mapM fun (name, row) => do
    let text := String.intercalate "\t" (← table ctx.project name)[0]!.toList ++ "\n" ++ String.intercalate "\t" row.toList
    IO.FS.writeFile (adapterCurrent / "registry" / name) text
    pure (name,text)
  expectAction ctx "adapter-current-populated" true (adaptEmpty ctx adapterCurrent)
  for (name, text) in original do
    ensure ((← IO.FS.readFile (adapterCurrent / "registry" / name)) == text) "adapter changed current bytes"
  for name in #["bindings.tsv", "axioms.tsv"] do
    let target ← copy ("adapter-old-populated-" ++ name) oldSchema
    add target name #["populated", "historical", "artifact", "rows", "must", "be", "preserved"]
    expectAction ctx ("adapter-old-populated-" ++ name) false (adaptEmpty ctx target)
      ("cannot migrate populated historical R4 fixture: " ++ name)
  for (name, row, diagnostic) in #[
      ("statement-modules.tsv", #["LatticeSystem.Claims.Front", "LatticeSystem/Claims/Front.lean", "leaf"], "R4 artifact"),
      ("axioms.tsv", #["AX-RUNTIME-0001", "LatticeSystem.Axioms.State.fixture", "LatticeSystem.Axioms.State", "state", "fixture", "fixture", "reopen", "PENDING"], "axiom artifact")] do
    let before ← copy ("populated-" ++ name ++ "-base") base
    let after ← copy ("populated-" ++ name ++ "-current") current
    for target in #[before, after] do add target name row
    let rows ← table after name
    writeTable after name <| rows.set! 0 ((rows[0]!).set! (rows[0]!.size - 1) (rows[0]!.back! ++ "_drift"))
    transition ctx ("populated-artifact-header-drift-" ++ name) before after false diagnostic
  transition ctx "omitted-claim-new-item" base omitted
  transition ctx "two-omissions-one-named-item" base grouped
  static ctx "pending-old-static" current
  discard <| expect ctx "pending-old-registry" true (ctx.gate "registry" current)
  baseDiff ctx "pending-old-dedicated-diff" base current true am.event
  baseDiff ctx "ordinary-content-change-rejected" base current false
  baseDiff ctx "later-ordinary-after-event" current current
  baseDiff ctx "historical-event-cannot-reopen-exception" current current true am.event
  let frozenBase ← copy "frozen-base" base
  mutate frozenBase "claims.tsv" claim 8 (← blob ctx old[7]!)
  refresh ctx frozenBase
  transition ctx "frozen-old-content-event" frozenBase current
  baseDiff ctx "frozen-old-dedicated-diff" frozenBase current true am.event
  let existing ← table base "claim-content-amendments.tsv"
  let snapshot := (← git ctx.project #["rev-parse", "HEAD"]).trimAscii.toString
  let snapshot ← if existing.size > 1 then do
    let events ← table base "correction-events.tsv"
    let (_,snapshot) := (existing.extract 1 existing.size).foldl (fun (minimum,snapshot) ca =>
      let event := (events.find? fun r => r[0]?.getD "" == ca[1]!).get!
      if event[1]!.toNat! < minimum then (event[1]!.toNat!,event[3]!) else (minimum,snapshot))
      (1000000000,snapshot)
    pure snapshot
    else pure snapshot
  let historicalHeader := ctx.temporary / "pre-amendment-header"
  cloneCommit ctx snapshot historicalHeader
  ensure ((← table historicalHeader "claim-content-amendments.tsv").size == 1) "historical empty amendment schema"
  ensure (!(← table historicalHeader "claim-corrections.tsv").any (fun r => r[5]?.getD "" == "amend_content")) "historical amendment action"
  let legacyBase ← copy "historical-no-ledger" historicalHeader
  IO.FS.removeFile (legacyBase / "registry/claim-content-amendments.tsv")
  let legacyCurrent := ctx.temporary / "historical-content-event"
  let legacy ← prepareAmendment ctx legacyBase legacyCurrent content
  transition ctx "historical-no-ledger-content-event" legacyBase legacyCurrent
  baseDiff ctx "historical-no-ledger-dedicated-diff" legacyBase legacyCurrent true legacy.event
  baseDiff ctx "ordinary-header-only-migration" legacyBase historicalHeader
  baseDiff ctx "ordinary-data-without-event" legacyBase legacyCurrent false
  pure (frozenBase, legacyBase)

/-- Reject incomplete provenance, stale hashes, metadata drift and extraneous creators. -/
def amendmentManifestCases (ctx : Context) (base current frozenBase : FilePath) (am : Amendment) : IO Unit := do
  let copy := caseCopy ctx
  let old := am.old
  let missing ← copy "missing-ledger" current
  IO.FS.removeFile (missing / "registry/claim-content-amendments.tsv")
  transition ctx "missing-current-ledger" base missing false "missing registry/claim-content-amendments.tsv"
  let missingRow ← copy "missing-row" current
  remove missingRow "claim-content-amendments.tsv" am.amendment
  transition ctx "missing-amendment-row" base missingRow false "missing its provenance row"
  let duplicate ← copy "duplicate-amendment" current
  add duplicate "claim-content-amendments.tsv" (← table duplicate "claim-content-amendments.tsv").back!
  static ctx "duplicate-amendment-rejected" duplicate false "duplicate content amendment"
  for (name, column, value, diagnostic) in #[
      ("invalid-id", 0, "CA-invalid-1", "bad content amendment ID"),
      ("unknown-event", 1, "UNKNOWN-EVENT", "ownership mismatch"),
      ("unknown-correction", 2, "CC-UNKNOWN-0001", "ownership mismatch"),
      ("wrong-claim", 3, "CL-TASAKI2020-0002", "ownership mismatch"),
      ("pending-old-ledger", 4, "PENDING", "requires frozen"),
      ("pending-new-ledger", 5, "PENDING", "requires frozen"),
      ("wrong-page-source", 6, String.ofList (List.replicate 40 'a'), "page source mismatch"),
      ("pending-page-source", 6, "PENDING", "page source mismatch"),
      ("wrong-review", 7, "WRONG-REVIEW", "review ownership mismatch")] do
    let target ← copy name current
    mutate target "claim-content-amendments.tsv" am.amendment column value
    static ctx name target false diagnostic
  for (name, file, id, col, value, label, diagnostic) in #[
      ("wrong-action", "claim-corrections.tsv", am.correction, 5, "reclassify", "amendment-owned-by-wrong-action", "ownership mismatch"),
      ("wrong-source", "correction-events.tsv", am.event, 2, "OTHER", "cross-source-event", "source mismatch")] do
    let target ← copy name current
    mutate target file id col value
    static ctx label target false diagnostic
  let staleOld ← copy "stale-old" current
  mutate staleOld "claim-content-amendments.tsv" am.amendment 4 (String.ofList (List.replicate 40 '1'))
  transition ctx "stale-old-content-hash" base staleOld false "old content OID is stale"
  let staleBase ← copy "stale-recorded-old" frozenBase
  mutate staleBase "claims.tsv" claim 8 (String.ofList (List.replicate 40 '2'))
  refresh ctx staleBase
  transition ctx "stale-frozen-old-record" staleBase current false "old content OID is stale"
  let staleNew ← copy "stale-new" current
  mutate staleNew "claim-content-amendments.tsv" am.amendment 5 (String.ofList (List.replicate 40 '3'))
  transition ctx "stale-new-content-hash" base staleNew false "new content OID is stale"
  let pendingNew ← copy "pending-new-record" current
  mutate pendingNew "claims.tsv" claim 8 "PENDING"
  transition ctx "pending-new-claim-record" base pendingNew false "new content OID is stale"
  for (name, text, diagnostic) in #[("no-op", old[7]!, "no-op"), ("surrogate-true", "True.", "contentless"),
      ("surrogate-false", "False", "contentless"), ("surrogate-empty", "", "contentless")] do
    let target ← copy name current
    mutate target "claims.tsv" claim 7 text
    mutate target "claims.tsv" claim 8 (← blob ctx text)
    mutate target "claim-content-amendments.tsv" am.amendment 5 (← blob ctx text)
    refresh ctx target
    transition ctx name base target false diagnostic
  for (name, col, value) in #[("id", 0, "CL-TASAKI2020-9999"), ("order", 2, "000015.0099"),
      ("page", 3, "PG-TASAKI2020-0016"), ("locator", 4, "unreviewed-locator"),
      ("classification", 5, "assertion"), ("subkind", 6, "theorem"),
      ("exclusion", 9, "new-exclusion"), ("tombstone", 11, "true")] do
    let target ← copy ("metadata-" ++ name) current
    mutate target "claims.tsv" claim col value
    refresh ctx target
    transition ctx ("frozen-" ++ name) base target false
  let unowned ← copy "unowned-other-claim" current
  mutate unowned "claims.tsv" "CL-TASAKI2020-0002" 7 "An unrelated unreviewed assertion."
  refresh ctx unowned
  transition ctx "unowned-other-content-change" base unowned false "unmanifested claim drift"
  for (name, row) in #[
      ("claim-successors.tsv", #["SE-RUNTIME-0001", am.event, am.correction, claim, "1", "new_successor", "CL-TASAKI2020-0002"]),
      ("source-item-additions.tsv", #["IA-RUNTIME-0001", am.event, am.correction, "1", "IT-RUNTIME-0001", am.review])] do
    let target ← copy ("extra-" ++ name) current
    add target name row
    static ctx ("amendment-cannot-add-" ++ name) target false "cannot introduce successors or source items"

/-- Check source eligibility, vocabulary review, immutable history and source isolation. -/
def amendmentHistoryCases (ctx : Context) (base current : FilePath) (am : Amendment)
    (initialOffset : Nat) : IO Unit := do
  let copy := caseCopy ctx
  let old := am.old
  let lateBase ← copy "late-base" base
  let lateCurrent ← copy "late-current" current
  for target in #[lateBase, lateCurrent] do mutate target "source-progress.tsv" "TASAKI2020" 1 "skeleton_frozen"
  transition ctx "late-stage-source" lateBase lateCurrent false "requires a pre-R4 source"
  let boundBase ← copy "bound-base" base
  let boundCurrent ← copy "bound-current" current
  for target in #[boundBase, boundCurrent] do add target "bindings.tsv" (← bindingRow boundBase "CL-TASAKI2020-0002")
  transition ctx "already-bound-other-claim-in-source" boundBase boundCurrent false "source already has bindings"
  for (name, row) in #[("slices.tsv", #["SL-RUNTIME-0001", "1", claim]),
      ("dependencies.tsv", #[claim, "requires", "CL-TASAKI2020-0002", "NONE"]),
      ("dependencies.tsv", #["CL-TASAKI2020-0002", "consequence_of", claim, "NONE"]),
      ("claim-axioms.tsv", #[claim, "AX-PROJECT-0001"])] do
    let suffix := name ++ toString ((← ctx.accepted.get) + (← ctx.rejected.get) - initialOffset)
    let before ← copy ("scope-base-" ++ suffix) base
    let after ← copy ("scope-current-" ++ suffix) current
    for target in #[before, after] do add target name row
    transition ctx ("existing-target-" ++ suffix) before after false "skeleton or axiom relations"
  let staleReview ← copy "unrefreshed-vocab-review" current
  mutate staleReview "claim-vocabulary-review.tsv" claim 2 (← record base "claim-vocabulary-review.tsv" claim)[2]!
  transition ctx "unrefreshed-vocabulary-review" base staleReview false "refreshed vocabulary review"
  let vocabBasis ← copy "vocab-basis" current
  mutate vocabBasis "claim-vocabulary-review.tsv" claim 1 "project_vocabulary"
  transition ctx "vocabulary-review-basis-drift" base vocabBasis false "refreshed vocabulary review"
  let vocabUse ← copy "vocab-use" current
  add vocabUse "claim-vocabulary.tsv" #[claim, "VO-TASAKI2020-0001"]
  transition ctx "vocabulary-use-drift" base vocabUse false "changed vocabulary use"
  let wrongCounts ← copy "wrong-census-count" current
  let n := (← record wrongCounts "source-invariants.tsv" "TASAKI2020")[2]!.toNat!
  mutate wrongCounts "source-invariants.tsv" "TASAKI2020" 2 (toString (n + 1))
  transition ctx "stale-census-count" base wrongCounts false "census invariant count is stale"
  let later := ctx.temporary / "later-event"
  let second ← prepareAmendment ctx current later "For every admissible x, F(x) = conjugate(\"G(x)\") + ε."
  static ctx "later-event-history-static" later
  transition ctx "repeat-amendment-exact-new-base" current later
  baseDiff ctx "repeat-amendment-dedicated-route" current later true second.event
  baseDiff ctx "repeat-amendment-ordinary-route-rejects" current later false
  baseDiff ctx "later-ordinary-freezes-both-events" later later
  let historical ← copy "historical-amendment-drift" later
  mutate historical "claim-content-amendments.tsv" am.amendment 7 "HISTORICAL-DRIFT"
  transition ctx "historical-row-mutation" current historical false "historical correction ledger drift"
  let staleChain ← copy "history-chain-stale" later
  mutate staleChain "claim-content-amendments.tsv" second.amendment 4 (← blob ctx old[7]!)
  static ctx "stale-history-chain" staleChain false "history chain is stale"
  let multiBase ← copy "multi-base" base
  let multiCurrent ← copy "multi-current" current
  for target in #[multiBase, multiCurrent] do
    let sources ← table target "sources.tsv"
    let extra := sources[1]! |>.set! 0 "SRB" |>.set! 2 "2" |>.set! 4 "SRB2026" |>.set! 12 "source-b" |>.set! 13 "runtime-source-b.pdf"
    add target "sources.tsv" extra
    add target "source-progress.tsv" #["SRB", "registered", "RUNTIME-SOURCE-B-REVIEW"]
  transition ctx "unrelated-source-preserved" multiBase multiCurrent
  let foreign ← copy "foreign-source-drift" multiCurrent
  mutate foreign "sources.tsv" "SRB" 5 "unreviewed-source-title"
  transition ctx "unrelated-source-drift-rejected" multiBase foreign false "unrelated frozen registry drift"
  let piggy ← copy "historical-ledger-piggyback" later
  let rows ← table piggy "claim-content-amendments.tsv"
  writeTable piggy "claim-content-amendments.tsv" <| rows.set! (rows.size - 1)
    (rows.back!.set! 0 (← unusedId later "claim-content-amendments.tsv" "CA-PIGGYBACK"))
  baseDiff ctx "historical-event-no-ordinary-bypass" later piggy false second.event "historical correction ledger drift"

/-- Check independently owned omissions, later repairs and simultaneous source actions. -/
def omissionHistoryCases (ctx : Context) (base omitted : FilePath) (am : Amendment)
    (om : Omission) : IO (FilePath × Omission × String) := do
  let copy := caseCopy ctx
  let old := am.old
  let page := am.page
  let content := "For every admissible x, F(x) = G(x)."
  static ctx "omitted-claim-static" omitted
  discard <| expect ctx "omitted-claim-registry" true (ctx.gate "registry" omitted)
  discard <| expect ctx "omitted-claim-item-contract" true (ctx.gate "source-items" omitted)
  baseDiff ctx "omitted-claim-dedicated-route" base omitted true om.event
  baseDiff ctx "omitted-claim-ordinary-rejected" base omitted false "" "frozen invariants regression"
  baseDiff ctx "omitted-claim-later-ordinary-freeze" omitted omitted
  baseDiff ctx "omitted-claim-no-historical-exception" omitted omitted true om.event
  let existingItem := ctx.temporary / "omitted-existing-item"
  discard <| prepareOmission ctx base existingItem false
  transition ctx "omitted-claim-existing-item" base existingItem
  discard <| expect ctx "omitted-existing-item-contract" true (ctx.gate "source-items" existingItem)
  let mixed ← copy "mixed-addition-amendment" omitted
  let nr ← unusedId mixed "claim-normalization-reviews.tsv" "NR-RUNTIME"
  let cc ← unusedId mixed "claim-corrections.tsv" "CC-RUNTIME"
  let ca ← unusedId mixed "claim-content-amendments.tsv" "CA-RUNTIME"
  add mixed "claim-normalization-reviews.tsv" #[nr, om.event, "2", claim, "exact_statement_readiness", "amend_content", "closed", "restore-source-condition", om.review]
  add mixed "claim-corrections.tsv" #[cc, om.event, "2", nr, claim, "amend_content", old[5]!, old[6]!, old[5]!, old[6]!]
  add mixed "claim-content-amendments.tsv" #[ca, om.event, cc, claim, ← blob ctx old[7]!, ← blob ctx content, page[9]!, om.review]
  mutate mixed "claims.tsv" claim 7 content
  mutate mixed "claims.tsv" claim 8 (← blob ctx content)
  mutate mixed "claim-vocabulary-review.tsv" claim 2 om.review
  refresh ctx mixed
  transition ctx "mixed-addition-and-amendment" base mixed
  baseDiff ctx "mixed-addition-and-amendment-route" base mixed true om.event
  let addedLater := ctx.temporary / "added-claim-later-amendment"
  let added ← prepareAmendment ctx omitted addedLater "The two finite classes have a common size." om.claim
  transition ctx "historical-added-claim-later-amended" omitted addedLater
  static ctx "historical-addition-static-after-amendment" addedLater
  baseDiff ctx "historical-addition-amendment-route" omitted addedLater true added.event
  let reclassified ← copy "added-claim-later-reclassified" omitted
  let re := "RUNTIME-ADDED-RECLASSIFY"
  let rr := re ++ "-REVIEW"
  add reclassified "correction-events.tsv" #[re, toString (← table reclassified "correction-events.tsv").size,
    "TASAKI2020", (← git ctx.project #["rev-parse", "HEAD"]).trimAscii.toString, rr]
  let nr ← unusedId reclassified "claim-normalization-reviews.tsv" "NR-RUNTIME"
  let cc ← unusedId reclassified "claim-corrections.tsv" "CC-RUNTIME"
  add reclassified "claim-normalization-reviews.tsv" #[nr, re, "1", om.claim, "exact_statement_readiness", "reclassify", "closed", "refine-source-classification", rr]
  add reclassified "claim-corrections.tsv" #[cc, re, "1", nr, om.claim, "reclassify", "assertion", "unnumbered_obligation", "definition", "definition"]
  mutate reclassified "claims.tsv" om.claim 5 "definition"
  mutate reclassified "claims.tsv" om.claim 6 "definition"
  mutate reclassified "claim-vocabulary-review.tsv" om.claim 2 rr
  refresh ctx reclassified
  transition ctx "historical-added-claim-later-reclassified" omitted reclassified
  static ctx "historical-addition-static-after-reclassification" reclassified
  let addedBound ← copy "historical-addition-after-r4" omitted
  mutate addedBound "source-progress.tsv" "TASAKI2020" 1 "skeleton_frozen"
  add addedBound "bindings.tsv" (← bindingRow addedBound om.claim)
  static ctx "historical-addition-static-after-r4" addedBound
  let projectVocab ← copy "addition-project-vocabulary" omitted
  mutate projectVocab "claim-vocabulary-review.tsv" om.claim 1 "project_vocabulary"
  add projectVocab "claim-vocabulary.tsv" #[om.claim, "VO-TASAKI2020-0001"]
  transition ctx "addition-reviewed-existing-project-vocabulary" base projectVocab
  let two := ctx.temporary / "two-additions"
  let om2 ← prepareOmission ctx omitted two
  remove two "correction-events.tsv" om2.event
  for (name, id) in #[("claim-normalization-reviews.tsv", om2.normalization), ("claim-corrections.tsv", om2.correction)] do
    mutate two name id 1 om.event
    mutate two name id 2 "2"
  mutate two "claim-normalization-reviews.tsv" om2.normalization 8 om.review
  let ia2 := (← table two "source-item-additions.tsv").back![0]!
  mutate two "source-item-additions.tsv" ia2 1 om.event
  mutate two "source-item-additions.tsv" ia2 5 om.review
  mutate two "claim-vocabulary-review.tsv" om2.claim 2 om.review
  mutate two "source-invariants.tsv" "TASAKI2020" 7 om.review
  transition ctx "two-owned-omitted-claims" base two
  let foreignOwner ← copy "addition-valid-foreign-item-owner" two
  let ia1 := (← table omitted "source-item-additions.tsv").back![0]!
  mutate foreignOwner "source-item-additions.tsv" ia1 2 om2.correction
  mutate foreignOwner "source-item-additions.tsv" ia2 3 "2"
  transition ctx "addition-valid-foreign-item-owner" base foreignOwner false "new source item contains a successor from a different correction"
  pure (two, om2, ia1)

/-- Check canonical ownership and public grouping of independently created shared-item members. -/
def groupedOwnershipCases (ctx : Context) (base grouped : FilePath) (am : Amendment)
    (gr : Grouped) : IO Unit := do
  let copy := caseCopy ctx
  let page := am.page
  let nr2 := gr.second.normalization
  let cc2 := gr.second.correction
  let secondClaim := gr.second.claim
  let groupedIa := (← table grouped "source-item-additions.tsv").back![0]!
  let groupedItem := gr.first.item
  let anchor ← record grouped "source-items.tsv" groupedItem
  static ctx "grouped-omissions-static" grouped
  baseDiff ctx "grouped-omissions-dedicated-route" base grouped true gr.first.event
  baseDiff ctx "grouped-omissions-ordinary-rejected" base grouped false "" "frozen invariants regression"
  baseDiff ctx "grouped-omissions-later-ordinary-freeze" grouped grouped
  baseDiff ctx "grouped-omissions-historical-event-is-ordinary" grouped grouped true gr.first.event
  expectAction ctx "grouped-generator-contract" true (groupedPublic ctx base grouped gr)
  let reversed ← copy "grouped-correction-position-independent" grouped
  let rows ← table reversed "claim-corrections.tsv"
  writeTable reversed "claim-corrections.tsv" <| rows.extract 0 (rows.size - 2) ++
    #[rows.back!.set! 2 "1", rows[rows.size - 2]!.set! 2 "2"]
  transition ctx "grouped-owner-is-first-relation-not-correction-position" base reversed
  let otherPage := ((← table base "pages.tsv").find? fun r => r[0]?.getD "" != page[0]! && r[0]?.getD "" != "page_id").get![0]!
  for (label, name, id, col, value, diagnostic) in #[
      ("noncanonical-owner", "source-item-additions.tsv", groupedIa, 2, cc2, "new source item contains a successor from a different correction"),
      ("secondary-open-review", "claim-normalization-reviews.tsv", nr2, 6, "open", "invalid claim normalization review ledger"),
      ("secondary-source", "claims.tsv", secondClaim, 1, "SRB", "normalization review source mismatch"),
      ("secondary-page", "claims.tsv", secondClaim, 3, otherPage, "source item mismatch"),
      ("secondary-review-token", "claim-vocabulary-review.tsv", secondClaim, 2, "WRONG-REVIEW", "reviewed vocabulary basis and use"),
      ("relation-position", "item-claims.tsv", groupedItem, 1, "3", "item relation positions are not contiguous"),
      ("first-claim-order", "source-items.tsv", groupedItem, 2, anchor[2]! ++ ".0001", "item order does not match first claim"),
      ("reused-item", "source-item-additions.tsv", groupedIa, 4, (← table base "source-items.tsv")[1]![0]!, "source item addition reuses a frozen item ID")] do
    let target ← copy ("grouped-" ++ label) grouped
    mutate target name id col value
    transition ctx ("grouped-" ++ label) base target false diagnostic
  for missing in #["creator", "review", "both"] do
    let target ← copy ("grouped-secondary-missing-" ++ missing) grouped
    if missing != "review" then remove target "claim-corrections.tsv" cc2
    if missing != "creator" then remove target "claim-normalization-reviews.tsv" nr2
    transition ctx ("grouped-secondary-missing-" ++ missing) base target false
      (if missing == "both" then "split successor provenance is incomplete" else "invalid claim correction ledger")
  let foreignEvent ← copy "grouped-foreign-event" grouped
  let events ← table foreignEvent "correction-events.tsv"
  let oe := "RUNTIME-FOREIGN-OMISSION"
  let ore := oe ++ "-REVIEW"
  add foreignEvent "correction-events.tsv" #[oe, toString events.size, "TASAKI2020", events.back![3]!, ore]
  for (name, id) in #[("claim-normalization-reviews.tsv", nr2), ("claim-corrections.tsv", cc2)] do
    mutate foreignEvent name id 1 oe
    mutate foreignEvent name id 2 "1"
  mutate foreignEvent "claim-normalization-reviews.tsv" nr2 8 ore
  mutate foreignEvent "claim-vocabulary-review.tsv" secondClaim 2 ore
  transition ctx "grouped-secondary-foreign-event" base foreignEvent false "correction event is not reviewed"
  let reordered ← copy "grouped-reordered-relation-rows" grouped
  let relations ← table reordered "item-claims.tsv"
  let index := ((List.range relations.size).find? fun i => relations[i]![0]! == groupedItem).get!
  writeTable reordered "item-claims.tsv" <| (relations.set! index relations[index + 1]!).set! (index + 1) relations[index]!
  mutate reordered "source-item-additions.tsv" groupedIa 2 cc2
  transition ctx "grouped-reordered-relation-rows" base reordered false "item relation positions are not contiguous"
  let frozenMember ← copy "grouped-frozen-member" grouped
  let relations ← table frozenMember "item-claims.tsv"
  let index := ((List.range relations.size).filter fun i => relations[i]![0]! == groupedItem).getLast!
  writeTable frozenMember "item-claims.tsv" <| relations.extract 0 (index + 1) ++
    #[#[groupedItem, "3", claim]] ++ relations.extract (index + 1) relations.size
  transition ctx "grouped-frozen-member" base frozenMember false "new source item contains a frozen predecessor claim"
  let duplicateMember ← copy "grouped-secondary-duplicate-use" grouped
  let oldItem := (← table base "source-items.tsv")[1]![0]!
  let relations ← table duplicateMember "item-claims.tsv"
  let index := ((List.range relations.size).filter fun i => relations[i]![0]! == oldItem).getLast!
  let position := 1 + (relations.filter (fun r => r[0]?.getD "" == oldItem)).foldl (fun n r => max n r[1]!.toNat!) 0
  writeTable duplicateMember "item-claims.tsv" <| relations.extract 0 (index + 1) ++
    #[#[oldItem, toString position, secondClaim]] ++ relations.extract (index + 1) relations.size
  transition ctx "grouped-secondary-duplicate-use" base duplicateMember false "exactly one source item"
  let duplicateIa ← copy "grouped-duplicate-manifest" grouped
  let extra := (← table duplicateIa "source-item-additions.tsv").back! |>.set! 0
    (← unusedId duplicateIa "source-item-additions.tsv" "IA-RUNTIME") |>.set! 3 "2"
  add duplicateIa "source-item-additions.tsv" extra
  transition ctx "grouped-duplicate-manifest" base duplicateIa false "source item is manifested more than once"

/-- Check split/omission ownership separation and later immutable shared-item history. -/
def groupedHistoryCases (ctx : Context) (base grouped two : FilePath) (gr : Grouped)
    (om om2 : Omission) (ia1 : String) : IO Unit := do
  let copy := caseCopy ctx
  let cc2 := gr.second.correction
  let firstClaim := gr.first.claim
  let secondClaim := gr.second.claim
  let groupedIa := (← table grouped "source-item-additions.tsv").back![0]!
  let groupedItem := gr.first.item
  let splitItems ← copy "independent-split-and-omission-items" two
  let predecessor ← record base "claims.tsv" claim
  mutate splitItems "claim-normalization-reviews.tsv" om2.normalization 3 claim
  mutate splitItems "claim-normalization-reviews.tsv" om2.normalization 5 "split"
  for (col, value) in #[(4, claim), (5, "split"), (6, predecessor[5]!), (7, predecessor[6]!), (8, predecessor[5]!), (9, predecessor[6]!)] do
    mutate splitItems "claim-corrections.tsv" om2.correction col value
  for (col, value) in #[(11, "true"), (12, om2.claim), (13, "omitted-source-assertion"), (14, om.review)] do
    mutate splitItems "claims.tsv" claim col value
  remove splitItems "claim-vocabulary-review.tsv" claim
  add splitItems "claim-successors.tsv" #[← unusedId splitItems "claim-successors.tsv" "CS-RUNTIME", om.event,
    om2.correction, claim, "1", "new_successor", om2.claim]
  refresh ctx splitItems
  transition ctx "independently-owned-split-and-omission-items" base splitItems
  let mixedGroup ← copy "split-member-in-omission-item" splitItems
  let secondItem := ((← table mixedGroup "item-claims.tsv").find? fun r => r[2]?.getD "" == om2.claim).get![0]!
  remove mixedGroup "source-items.tsv" secondItem
  remove mixedGroup "source-item-additions.tsv" secondItem 4
  mutate mixedGroup "item-claims.tsv" secondItem 0 om.item
  let records ← table mixedGroup "item-claims.tsv"
  writeTable mixedGroup "item-claims.tsv" <| records.map fun r => if r[2]?.getD "" == om2.claim then r.set! 1 "2" else r
  transition ctx "split-member-in-omission-item" base mixedGroup false "new source item contains a successor from a different correction"
  let splitOwner ← copy "omission-member-in-split-item" mixedGroup
  mutate splitOwner "source-item-additions.tsv" ia1 2 om2.correction
  transition ctx "omission-member-in-split-item" base splitOwner false "new source item contains a successor from a different correction"
  for (label, name, id, col, value, diagnostic) in #[
      ("IA-owner", "source-item-additions.tsv", groupedIa, 2, cc2, "historical correction ledger drift"),
      ("metadata", "source-items.tsv", groupedItem, 6, "Changed title", "source item identity/order/label regression")] do
    let target ← copy ("grouped-later-frozen-" ++ label) grouped
    mutate target name id col value
    baseDiff ctx ("grouped-later-frozen-" ++ label) grouped target false "" diagnostic
  for member in #[firstClaim, secondClaim] do
    let target ← copy ("grouped-later-relation-" ++ member) grouped
    remove target "item-claims.tsv" member 2
    baseDiff ctx ("grouped-later-relation-" ++ member) grouped target false "" "item-claim regression"
  let groupedLater := ctx.temporary / "grouped-later-amendment"
  let gl ← prepareAmendment ctx grouped groupedLater "The second synthetic test family has positive size." secondClaim
  for name in #["source-items.tsv", "item-claims.tsv", "source-item-additions.tsv"] do
    ensure ((← table groupedLater name) == (← table grouped name)) "grouped later item preservation"
  ensure ((← record groupedLater "claims.tsv" firstClaim) == (← record grouped "claims.tsv" firstClaim)) "grouped first member preserved"
  transition ctx "grouped-historical-member-amendment" grouped groupedLater
  static ctx "grouped-historical-member-amendment-static" groupedLater
  baseDiff ctx "grouped-historical-member-amendment-route" grouped groupedLater true gl.event

/-- Reject malformed omission creation, readiness, item, vocabulary and census records. -/
def omissionRejectionCases (ctx : Context) (base omitted : FilePath) (am : Amendment)
    (om : Omission) (ia1 : String) : IO Unit := do
  let copy := caseCopy ctx
  let page := am.page
  for (label, name, id, col, value, diagnostic) in #[
      ("addition-existing-id", "claim-normalization-reviews.tsv", om.normalization, 3, claim, "invalid claim correction ledger"),
      ("addition-wrong-old-kind", "claim-corrections.tsv", om.correction, 6, "assertion", "invalid omitted claim classification"),
      ("addition-wrong-old-subkind", "claim-corrections.tsv", om.correction, 7, "equation", "invalid omitted claim classification"),
      ("addition-wrong-new-kind", "claim-corrections.tsv", om.correction, 8, "definition", "classification does not match"),
      ("addition-out-of-scope", "claim-corrections.tsv", om.correction, 8, "out_of_scope", "invalid omitted claim classification"),
      ("addition-review-open", "claim-normalization-reviews.tsv", om.normalization, 6, "open", "invalid claim normalization review ledger"),
      ("addition-review-scope", "claim-normalization-reviews.tsv", om.normalization, 4, "proof_readiness", "invalid claim normalization review ledger"),
      ("addition-review-token", "claim-normalization-reviews.tsv", om.normalization, 8, "WRONG-REVIEW", "invalid claim normalization review ledger"),
      ("addition-review-source", "claims.tsv", om.claim, 1, "SRB", "normalization review source mismatch"),
      ("addition-page-unknown", "claims.tsv", om.claim, 3, "PG-TASAKI2020-9999", "source page mismatch"),
      ("addition-page-hash-drift", "pages.tsv", page[0]!, 9, String.ofList (List.replicate 40 '0'), "unchanged frozen source page"),
      ("addition-pending-hash", "claims.tsv", om.claim, 8, "PENDING", "content OID is not frozen or is stale"),
      ("addition-stale-hash", "claims.tsv", om.claim, 8, String.ofList (List.replicate 40 '0'), "content OID is not frozen or is stale"),
      ("addition-content-surrogate", "claims.tsv", om.claim, 7, "True", "contentless omitted claim surrogate"),
      ("addition-tombstone", "claims.tsv", om.claim, 11, "true", "active formalization target"),
      ("addition-exclusion", "claims.tsv", om.claim, 9, "UNREVIEWED", "active formalization target"),
      ("addition-vocab-token", "claim-vocabulary-review.tsv", om.claim, 2, "WRONG-REVIEW", "reviewed vocabulary basis and use"),
      ("addition-vocab-basis", "claim-vocabulary-review.tsv", om.claim, 1, "project_vocabulary", "reviewed vocabulary basis and use"),
      ("addition-late-source", "source-progress.tsv", "TASAKI2020", 1, "skeleton_frozen", "requires a pre-R4 source"),
      ("addition-item-foreign-owner", "source-item-additions.tsv", ia1, 2, "CC-UNOWNED-0001", "source item addition event or correction mismatch"),
      ("addition-item-token", "source-item-additions.tsv", ia1, 5, "WRONG-REVIEW", "source item addition event or correction mismatch"),
      ("addition-unrelated-claim-drift", "claims.tsv", "CL-TASAKI2020-0003", 4, "unreviewed locator", "unmanifested claim drift"),
      ("addition-old-ledger-drift", "claim-corrections.tsv", (← table base "claim-corrections.tsv")[1]![0]!, 9, "definition", "historical correction ledger drift"),
      ("addition-invariant-review", "source-invariants.tsv", "TASAKI2020", 7, "WRONG-REVIEW", "event invariant review"),
      ("addition-physical-page-count", "source-invariants.tsv", "TASAKI2020", 1, "535", "physical page count is stale"),
      ("addition-source-fingerprint", "sources.tsv", "TASAKI2020", 14, "PENDING", "source fingerprints changed or are not frozen"),
      ("addition-claim-order", "claims.tsv", om.claim, 2, "invalid-order", "bad claim order key"),
      ("addition-item-position", "item-claims.tsv", om.item, 1, "2", "item relation positions are not contiguous")] do
    let target ← copy ("omission-" ++ label) omitted
    mutate target name id col value
    if label == "addition-claim-order" then refresh ctx target
    transition ctx label base target false diagnostic
  for (label, name, column, diagnostic) in #[
      ("addition-missing-item", "item-claims.tsv", 2, "exactly one source item"),
      ("addition-missing-vocab", "claim-vocabulary-review.tsv", 0, "reviewed vocabulary basis and use"),
      ("addition-missing-item-manifest", "source-item-additions.tsv", 2, "unmanifested source item addition"),
      ("addition-missing-correction", "claim-corrections.tsv", 0, "invalid claim correction ledger")] do
    let target ← copy label omitted
    remove target name (if #["claim-corrections.tsv", "source-item-additions.tsv"].contains name then om.correction else om.claim) column
    transition ctx label base target false diagnostic
  let duplicateRelation ← copy "addition-duplicate-item-relation" omitted
  add duplicateRelation "item-claims.tsv" ((← table duplicateRelation "item-claims.tsv").find? fun r => r[2]?.getD "" == om.claim).get!
  transition ctx "addition-duplicate-item-relation" base duplicateRelation false "exactly one source item"
  let overlap ← copy "addition-successor-overlap" omitted
  add overlap "claim-successors.tsv" #["SE-RUNTIME-OMISSION-0001", om.event, om.correction, claim, "1", "new_successor", om.claim]
  transition ctx "addition-successor-overlap" base overlap false "cannot have successor provenance"
  for (label, name, row, diagnostic) in #[
      ("addition-r4-binding", "bindings.tsv", ← bindingRow omitted om.claim, "source already has bindings"),
      ("addition-slice", "slices.tsv", #["SL-RUNTIME-0001", "1", om.claim], "skeleton or axiom relations"),
      ("addition-dependency", "dependencies.tsv", #[om.claim, "requires", claim, "NONE"], "skeleton or axiom relations"),
      ("addition-reverse-dependency", "dependencies.tsv", #[claim, "required_by", om.claim, "REVIEW"], "skeleton or axiom relations"),
      ("addition-axiom", "claim-axioms.tsv", #[om.claim, "AX-RUNTIME-0001"], "skeleton or axiom relations"),
      ("addition-vocab-use", "claim-vocabulary.tsv", #[om.claim, "VO-TASAKI2020-0001"], "reviewed vocabulary basis and use")] do
    let target ← copy label omitted
    add target name row
    transition ctx label base target false diagnostic
  for action in #["reclassify", "exclude_nonclaim", "split", "amend_content"] do
    let target ← copy ("none-old-" ++ action) omitted
    mutate target "claim-normalization-reviews.tsv" om.normalization 5 action
    mutate target "claim-corrections.tsv" om.correction 5 action
    transition ctx ("none-old-invalid-for-" ++ action) base target false "correction predecessor source mismatch"
    if action != "amend_content" then
      static ctx ("none-old-static-invalid-for-" ++ action) target false "NONE old classification requires add_omitted_claim"
  let reused ← copy "addition-reuses-existing-id" omitted
  mutate reused "claim-normalization-reviews.tsv" om.normalization 3 claim
  mutate reused "claim-corrections.tsv" om.correction 4 claim
  transition ctx "addition-reuses-existing-id" base reused false "must introduce a fresh claim ID"
  let missingClaim ← copy "addition-missing-claim" omitted
  remove missingClaim "claims.tsv" om.claim
  transition ctx "addition-missing-claim" base missingClaim false "must introduce a fresh claim ID"
  let unowned ← copy "addition-unowned-claim" omitted
  let rows ← table unowned "claims.tsv"
  let originalClaimRow ← record unowned "claims.tsv" om.claim
  let extra := originalClaimRow |>.set! 0 (← unusedId unowned "claims.tsv" "CL-TASAKI2020") |>.set! 2 (originalClaimRow[2]! ++ ".0001")
  writeTable unowned "claims.tsv" <| insertAfter rows (· == originalClaimRow) #[extra]
  transition ctx "addition-unowned-new-claim" base unowned false "split successor provenance is incomplete"
  for (column, diagnostic) in #[(2, "census invariant count is stale"), (3, "formalization target count is stale"), (6, "census OID is stale")] do
    let target ← copy ("addition-stale-invariant-" ++ toString column) omitted
    let invariant ← record target "source-invariants.tsv" "TASAKI2020"
    let value := if column == 6 then String.ofList (List.replicate 40 '0') else toString (invariant[column]!.toNat! + 1)
    mutate target "source-invariants.tsv" "TASAKI2020" column value
    transition ctx ("addition-stale-invariant-" ++ toString column) base target false diagnostic

/-- Execute the original amendment, omission and shared-item matrix in its original action order. -/
def initial (ctx : Context) (base current : FilePath) (am : Amendment)
    (omitted : FilePath) (om : Omission) (grouped : FilePath) (gr : Grouped) : IO FilePath := do
  let initialOffset := (← ctx.accepted.get) + (← ctx.rejected.get) - 1
  let (frozenBase, legacyBase) ← schemaHistoryCases ctx base current am omitted grouped
  amendmentManifestCases ctx base current frozenBase am
  amendmentHistoryCases ctx base current am initialOffset
  let (two, om2, ia1) ← omissionHistoryCases ctx base omitted am om
  groupedOwnershipCases ctx base grouped am gr
  groupedHistoryCases ctx base grouped two gr om om2 ia1
  omissionRejectionCases ctx base omitted am om ia1
  pure legacyBase

/-- Construct one content event with an optional simultaneous classification repair. -/
def contentEvent (ctx : Context) (before after : FilePath) (target : String)
    (pair : Option (String × String) := none) (text : Option String := none) : IO String := do
  let content := text.getD ("PRIVATE-COMBINED: F(\"x\") = G(x) + ε, stage " ++ after.fileName.getD "")
  let am ← prepareAmendment ctx before after content target
  if let some (kind, subkind) := pair then
    let nr := (← record after "claim-corrections.tsv" am.correction)[3]!
    mutate after "claim-normalization-reviews.tsv" nr 5 "amend_and_reclassify"
    mutate after "claim-corrections.tsv" am.correction 5 "amend_and_reclassify"
    for (col, value) in #[(5, kind), (6, subkind)] do
      mutate after "claims.tsv" target col value
      mutate after "claim-corrections.tsv" am.correction (col + 3) value
  mutate after "source-invariants.tsv" am.old[1]! 7 am.review
  refresh ctx after
  pure am.event

/-- Build a pure classification repair with content and content history preserved. -/
def reclassification (ctx : Context) (before after : FilePath) (target : String)
    (pair : String × String) : IO String := do
  let event ← contentEvent ctx before after target (some pair)
  let old ← record before "claims.tsv" target
  let cc := ((← table after "claim-corrections.tsv").find? fun r => r[1]?.getD "" == event).get!
  mutate after "claim-normalization-reviews.tsv" cc[3]! 5 "reclassify"
  mutate after "claim-corrections.tsv" cc[0]! 5 "reclassify"
  remove after "claim-content-amendments.tsv" cc[0]! 2
  for col in #[7, 8] do mutate after "claims.tsv" target col old[col]!
  refresh ctx after
  pure event

/-- Assert the independent byte, ownership, identity and derived-census oracle for an accepted step. -/
def assertContentStep (ctx : Context) (before after : FilePath) (event : String) : IO Unit := do
  let eventRow ← record after "correction-events.tsv" event
  for name in historyTables do
    let path := before / "registry" / name
    if ← path.pathExists then
      ensure ((← IO.FS.readFile (after / "registry" / name)).startsWith (← IO.FS.readFile path)) ("history prefix " ++ name)
  let corrections ← table after "claim-corrections.tsv"
  for cc in corrections.extract 1 corrections.size do
    if cc[1]! == event && #["amend_content", "amend_and_reclassify"].contains cc[5]! then
      let x := cc[4]!
      let old ← record before "claims.tsv" x
      let new ← record after "claims.tsv" x
      ensure (cc.extract 6 8 == old.extract 5 7 && cc.extract 8 10 == new.extract 5 7) "classification step ownership"
      ensure (old[7]! != new[7]! && (← blob ctx old[7]!) != (← blob ctx new[7]!)) "changed content bytes"
      let mutableColumns := if cc[5]! == "amend_and_reclassify" then #[5, 6, 7, 8] else #[7, 8]
      for i in [:old.size] do
        unless mutableColumns.contains i do ensure (old[i]! == new[i]!) "frozen claim metadata"
      if cc[5]! == "amend_and_reclassify" then ensure (old.extract 5 7 != new.extract 5 7) "changed classification pair"
      let nrs := (← table after "claim-normalization-reviews.tsv").filter fun r => r[1]?.getD "" == event && r[3]?.getD "" == x
      let ccs := corrections.filter fun r => r[1]?.getD "" == event && r[4]?.getD "" == x
      let cas := (← table after "claim-content-amendments.tsv").filter fun r => r[2]?.getD "" == cc[0]!
      ensure (nrs.size == 1 && ccs.size == 1 && cas.size == 1) "one content owner"
      let ca := cas[0]!
      ensure (ca.extract 4 6 == #[← blob ctx old[7]!, ← blob ctx new[7]!]) "exact blob hashes"
      ensure (new[8]! == ca[5]! && nrs[0]![8]! == ca[7]! && ca[7]! == eventRow[4]!) "review and hash ownership"
      ensure ((← record before "pages.tsv" old[3]!) == (← record after "pages.tsv" new[3]!)) "source page preserved"
      let relations := (← table before "item-claims.tsv").filter fun r => r[2]?.getD "" == x
      ensure (relations == (← table after "item-claims.tsv").filter (fun r => r[2]?.getD "" == x)) "item relations preserved"
      for relation in relations do
        ensure ((← record before "source-items.tsv" relation[0]!) == (← record after "source-items.tsv" relation[0]!)) "source item preserved"
  let pages := (← table after "pages.tsv").extract 1 (← table after "pages.tsv").size
  let claims := (← table after "claims.tsv").extract 1 (← table after "claims.tsv").size
  let invariant ← record after "source-invariants.tsv" eventRow[2]!
  let active := claims.filter fun r => r[1]! == eventRow[2]! && r[11]! == "false"
  let sourcePages := pages.filter fun r => r[1]! == eventRow[2]!
  ensure (invariant.extract 1 6 == #[toString sourcePages.size, toString active.size,
    toString (active.filter fun r => r[5]! != "out_of_scope").size,
    toString (active.filter fun r => r[6]! == "equation").size,
    toString (sourcePages.filter fun p => !active.any (fun r => r[3]! == p[0]!)).size]) "derived invariant counts"
  let selected := (pages ++ claims).filter fun r => r[1]! == eventRow[2]!
  let bytes := String.join <| selected.toList.map fun r => String.intercalate "\t" r.toList ++ "\n"
  ensure (invariant[6]! == (← blob ctx bytes) && invariant[7]! == eventRow[4]!) "derived invariant bytes and review"

/-- A fixture's exact base, current tree, owning event and target identity. -/
structure Fixture where
  before : FilePath
  after : FilePath
  event : String
  target : String

/-- Cache fixture families so historical chains share their original creating snapshots. -/
abbrev FixtureCache := IO.Ref (Array (String × Fixture))

/-- Construct a frozen synthetic classification base from the actual registered corpus. -/
def syntheticBase (ctx : Context) (name : String) (source : FilePath) : IO FilePath := do
  let target := ctx.temporary / ("combined-base-" ++ name)
  copyRegistry ctx source target
  mutate target "claims.tsv" claim 5 "assertion"
  mutate target "claims.tsv" claim 6 "equation"
  mutate target "claims.tsv" claim 8 (← blob ctx (← record target "claims.tsv" claim)[7]!)
  refresh ctx target
  pure target

/-- Construct all positive and historical combined-correction fixture families. -/
partial def fixture (ctx : Context) (cache : FixtureCache) (legacy : FilePath) (kind : String) : IO Fixture := do
  if let some entry := (← cache.get).find? (fun entry => entry.1 == kind) then return entry.2
  let after := ctx.temporary / ("combined-fixture-" ++ kind)
  let x := claim
  let (before,event,x) ← if #["F", "P", "D", "K", "V", "N", "A"].contains kind then do
      let before ← syntheticBase ctx kind (if kind == "N" then legacy else ctx.project)
      if kind == "P" then
        mutate before "claims.tsv" x 8 "PENDING"
        refresh ctx before
      if kind == "V" then
        mutate before "claim-vocabulary-review.tsv" x 1 "project_vocabulary"
        for id in #["VO-TASAKI2020-0001", "VO-TASAKI2020-0002"] do
          discard <| record ctx.project "vocabulary.tsv" id
          add before "claim-vocabulary.tsv" #[x, id]
      let pair := if kind == "A" then none else if kind == "D" then some ("definition", "equation")
        else if kind == "K" then some ("assertion", "lemma") else some ("definition", "definition")
      pure (before, ← contentEvent ctx before after x pair,x)
    else if kind == "Q" then do
      let f ← fixture ctx cache legacy "F"
      pure (f.before, ← reclassification ctx f.before after x ("definition", "definition"),x)
    else if kind == "W" then do
      let f ← fixture ctx cache legacy "V"
      copyFixture ctx f.after after
      let uses ← table after "claim-vocabulary.tsv"
      let indices := (List.range uses.size).filter fun i => i > 0 && uses[i]![0]! == x
      ensure (indices.length == 2) "two target vocabulary uses"
      writeTable after "claim-vocabulary.tsv" <| (uses.set! indices[0]! uses[indices[1]!]!).set! indices[1]! uses[indices[0]!]!
      let reviews ← table after "claim-vocabulary-review.tsv"
      let row ← record after "claim-vocabulary-review.tsv" x
      writeTable after "claim-vocabulary-review.tsv" <| (reviews.filter (· != row)).push row
      pure (f.before, f.event,x)
    else if kind == "M" then do
      let f ← fixture ctx cache legacy "F"
      let om ← prepareOmission ctx f.after after
      let ref := (← record after "correction-events.tsv" f.event)[4]!
      remove after "correction-events.tsv" om.event
      for (name, id) in #[("claim-normalization-reviews.tsv", om.normalization), ("claim-corrections.tsv", om.correction)] do
        mutate after name id 1 f.event
        mutate after name id 2 "2"
      mutate after "claim-normalization-reviews.tsv" om.normalization 8 ref
      let ia := ((← table after "source-item-additions.tsv").find? fun r => r[1]?.getD "" == om.event).get!
      mutate after "source-item-additions.tsv" ia[0]! 1 f.event
      mutate after "source-item-additions.tsv" ia[0]! 5 ref
      mutate after "claim-vocabulary-review.tsv" om.claim 2 ref
      mutate after "source-invariants.tsv" "TASAKI2020" 7 ref
      refresh ctx after
      let rows ← table after "claims.tsv"
      let index := ((List.range rows.size).find? fun i => rows[i]![0]! == om.claim).get!
      ensure (index < rows.size - 1) "nested omission inserted inside corpus"
      ensure ((← record after "claims.tsv" om.claim)[2]!.startsWith ((← record f.before "claims.tsv" x)[2]! ++ ".")) "nested omission key"
      pure (f.before, f.event,x)
    else if kind == "OC" then do
      let seed ← syntheticBase ctx kind ctx.project
      let before := ctx.temporary / "combined-omission-first"
      let om ← prepareOmission ctx seed before
      let x := om.claim
      pure (before, ← contentEvent ctx before after x (some ("definition", "definition")),x)
    else if #["CC", "CA", "AC", "CRAC", "CS", "CX"].contains kind then do
      let f ← fixture ctx cache legacy (if kind == "AC" then "A" else "F")
      let before ← if kind == "CRAC" then do
        let middle := ctx.temporary / "combined-middle-reclass"
        let me ← reclassification ctx f.after middle x ("domain", "domain")
        cache.modify (·.push ("CRAC-middle", ⟨f.after, middle, me, x⟩))
        pure middle
        else pure f.after
      let event ← if #["CA", "CRAC"].contains kind then contentEvent ctx before after x
        else if #["CC", "AC"].contains kind then do
          let pair := if kind == "CC" then ("assertion", "equation") else ("definition", "definition")
          contentEvent ctx before after x (some pair)
        else if kind == "CX" then do
          let e ← reclassification ctx before after x ("definition", "definition")
          let cc := ((← table after "claim-corrections.tsv").find? fun r => r[1]?.getD "" == e).get!
          let ref := (← record after "correction-events.tsv" e)[4]!
          let nr ← record after "claim-normalization-reviews.tsv" cc[3]!
          mutate after "claim-normalization-reviews.tsv" nr[0]! 5 "exclude_nonclaim"
          mutate after "claim-corrections.tsv" cc[0]! 5 "exclude_nonclaim"
          mutate after "claim-corrections.tsv" cc[0]! 8 "out_of_scope"
          for (col, value) in #[(5, "out_of_scope"), (9, nr[7]!), (10, ref)] do mutate after "claims.tsv" x col value
          remove after "claim-vocabulary-review.tsv" x
          remove after "claim-vocabulary.tsv" x
          refresh ctx after
          pure e
        else do
          let om ← prepareOmission ctx before after
          let old ← record before "claims.tsv" x
          mutate after "claim-normalization-reviews.tsv" om.normalization 3 x
          mutate after "claim-normalization-reviews.tsv" om.normalization 5 "split"
          for (col, value) in #[(4, x), (5, "split"), (6, old[5]!), (7, old[6]!), (8, old[5]!), (9, old[6]!)] do
            mutate after "claim-corrections.tsv" om.correction col value
          let nr ← record after "claim-normalization-reviews.tsv" om.normalization
          for (col, value) in #[(11, "true"), (12, om.claim), (13, nr[7]!), (14, om.review)] do mutate after "claims.tsv" x col value
          add after "claim-successors.tsv" #[← unusedId after "claim-successors.tsv" "SE-RUNTIME", om.event, om.correction, x, "1", "new_successor", om.claim]
          remove after "claim-vocabulary-review.tsv" x
          remove after "claim-vocabulary.tsv" x
          refresh ctx after
          pure om.event
      if #["CC", "CA", "AC", "CRAC"].contains kind then
        let history := (← table after "claim-content-amendments.tsv").filter fun r => r[3]?.getD "" == x
        ensure (history.size >= 2 && history[history.size - 2]![5]! == history.back![4]!) "historical content hash chain"
        ensure (history[history.size - 2]![5]! != (← record after "claims.tsv" x)[8]!) "historical content differs from current"
        if #["CC", "CRAC"].contains kind then
          let oldCc ← record after "claim-corrections.tsv" history[history.size - 2]![2]!
          ensure (oldCc.extract 8 10 != (← record after "claims.tsv" x).extract 5 7) "historical classification preserved"
      pure (before, event,x)
    else if kind == "HIST" then do
      let f ← fixture ctx cache legacy "CC"
      pure (f.after, ← contentEvent ctx f.after after x (some ("definition", "definition")),x)
    else throw <| IO.userError ("unknown fixture " ++ kind)
  assertContentStep ctx before after event
  let result : Fixture := ⟨before, after, event, x⟩
  cache.modify (·.push (kind, result))
  pure result
/-- Add an independent unchanged source as a control for cross-source isolation. -/
def secondSource (target : FilePath) : IO Unit := do
  let sources ← table target "sources.tsv"
  add target "sources.tsv" (sources[1]! |>.set! 0 "SRB" |>.set! 2 "2" |>.set! 4 "SRB2026" |>.set! 12 "source-b" |>.set! 13 "runtime-source-b.pdf")
  add target "source-progress.tsv" #["SRB", "registered", "RUNTIME-SOURCE-B-REVIEW"]

/-- Duplicate a content owner's review with its own stable identity and position. -/
def duplicateReview (after : FilePath) (nr : String) (action : String := "amend_and_reclassify") : IO String := do
  let row ← record after "claim-normalization-reviews.tsv" nr
  let id ← unusedId after "claim-normalization-reviews.tsv" "NR-DUPLICATE"
  add after "claim-normalization-reviews.tsv" (row |>.set! 0 id |>.set! 2 "2" |>.set! 5 action)
  pure id

/-- Apply exactly one named adversarial combined-correction mutation. -/
def mutateCombined (ctx : Context) (label : String) (before after : FilePath) (event x : String) : IO Unit := do
  let cc := ((← table after "claim-corrections.tsv").find? fun r => r[1]?.getD "" == event && r[4]?.getD "" == x).get!
  let nr := cc[3]!
  let ref := (← record after "correction-events.tsv" event)[4]!
  let ca := ((← table after "claim-content-amendments.tsv").find? fun r => r[2]?.getD "" == cc[0]!).getD #[]
  let other := ((← table before "claims.tsv").find? fun r =>
    r[1]?.getD "" == "TASAKI2020" && r[0]?.getD "" != x &&
      r[5]?.getD "" != "out_of_scope" && r[11]?.getD "" == "false").get![0]!
  let change := mutate after
  let caChange := mutate after "claim-content-amendments.tsv" (ca[0]?.getD "")
  let simple := #[
    ("combined-unknown-outcome", "claim-normalization-reviews.tsv", nr, 5, "unknown_action"),
    ("combined-unknown-action", "claim-corrections.tsv", cc[0]!, 5, "unknown_action"),
    ("combined-open-review", "claim-normalization-reviews.tsv", nr, 6, "open"),
    ("combined-wrong-scope", "claim-normalization-reviews.tsv", nr, 4, "census"),
    ("combined-wrong-outcome", "claim-normalization-reviews.tsv", nr, 5, "amend_content"),
    ("combined-static-ca-wrong-event", "claim-content-amendments.tsv", ca[0]?.getD "", 1, "UNKNOWN-EVENT"),
    ("combined-static-ca-wrong-correction", "claim-content-amendments.tsv", ca[0]?.getD "", 2, "CC-UNKNOWN-0001"),
    ("combined-static-ca-wrong-claim", "claim-content-amendments.tsv", ca[0]?.getD "", 3, other),
    ("combined-static-ca-wrong-review", "claim-content-amendments.tsv", ca[0]?.getD "", 7, "DIFFERENT-REVIEW"),
    ("combined-static-nr-wrong-outcome", "claim-normalization-reviews.tsv", nr, 5, "amend_content"),
    ("combined-static-nr-wrong-scope", "claim-normalization-reviews.tsv", nr, 4, "census"),
    ("combined-static-nr-open", "claim-normalization-reviews.tsv", nr, 6, "open"),
    ("combined-static-event-wrong-source", "correction-events.tsv", event, 2, "OTHER"),
    ("combined-frozen-order", "claims.tsv", x, 2, "000001.0999"),
    ("combined-frozen-locator", "claims.tsv", x, 4, "synthetic-altered-locator"),
    ("combined-source-identity-drift", "claims.tsv", x, 1, "OTHER"),
    ("combined-source-pin-drift", "sources.tsv", "TASAKI2020", 14, String.ofList (List.replicate 40 'a')),
    ("combined-vocabulary-basis-drift", "claim-vocabulary-review.tsv", x, 1, "project_vocabulary"),
    ("combined-vocabulary-stale-ref", "claim-vocabulary-review.tsv", x, 2, (← record before "claim-vocabulary-review.tsv" x)[2]!),
    ("combined-unrelated-vocabulary-review", "claim-vocabulary-review.tsv", other, 2, "CHANGED-REVIEW"),
    ("combined-invariant-review", "source-invariants.tsv", "TASAKI2020", 7, "WRONG-REVIEW")]
  for (name, file, id, col, value) in simple do
    if label == name then change file id col value; return
  if #["combined-static-missing-ca", "combined-missing-ca-integration"].contains label then
    remove after "claim-content-amendments.tsv" ca[0]!
  else if label == "combined-static-duplicate-ca" then add after "claim-content-amendments.tsv" ca
  else if #["combined-static-duplicate-owner-nr", "combined-duplicate-owner-integration"].contains label then
    discard <| duplicateReview after nr
  else if #["combined-static-duplicate-owner-cc", "combined-static-mixed-owner"].contains label then
    let row := cc |>.set! 0 (← unusedId after "claim-corrections.tsv" "CC-DUPLICATE") |>.set! 2 "2"
    let row ← if label.endsWith "mixed-owner" then do
      pure (row |>.set! 3 (← duplicateReview after nr "reclassify") |>.set! 5 "reclassify")
      else pure row
    add after "claim-corrections.tsv" row
  else if label.startsWith "combined-static-ca-owned-" then
    change "claim-corrections.tsv" cc[0]! 5 (label.replace "combined-static-ca-owned-" "")
  else if label.startsWith "combined-class-pair-no-op-" then
    let old ← record before "claims.tsv" x
    for col in #[5, 6] do
      change "claims.tsv" x col old[col]!
      change "claim-corrections.tsv" cc[0]! (col + 3) old[col]!
  else if label.startsWith "combined-wrong-" && ((label.splitOn "disposition-").length > 1 || (label.splitOn "subkind-").length > 1) then
    let which := String.intercalate "-" ((label.replace "combined-wrong-" "").splitOn "-").dropLast
    let (col, value) := if which == "old-disposition" then (6, "domain") else if which == "old-subkind" then (7, "lemma")
      else if which == "new-disposition" then (8, "notation") else (9, "theorem")
    change "claim-corrections.tsv" cc[0]! col value
  else if #["combined-static-none-old-disposition", "combined-static-none-old-subkind", "combined-static-old-out-of-scope",
      "combined-static-new-out-of-scope", "combined-static-illegal-new-kind", "combined-static-illegal-new-subkind"].contains label then
    let (col, value) := if label.endsWith "none-old-disposition" then (6, "NONE") else if label.endsWith "none-old-subkind" then (7, "NONE")
      else if label.endsWith "old-out-of-scope" then (6, "out_of_scope") else if label.endsWith "new-out-of-scope" then (8, "out_of_scope")
      else if label.endsWith "illegal-new-kind" then (8, "unrecognized") else (9, "unrecognized")
    change "claim-corrections.tsv" cc[0]! col value
  else if label == "legacy-amend-class-drift-static" then change "claim-corrections.tsv" cc[0]! 8 "definition"
  else if label == "legacy-amend-actual-class-drift-helper" then
    change "claims.tsv" x 5 "definition"
    change "claims.tsv" x 6 "definition"
  else if label == "legacy-reclass-content-drift" then
    let text := "Synthetic changed pure reclassification content"
    change "claims.tsv" x 7 text
    change "claims.tsv" x 8 (← blob ctx text)
    refresh ctx after
  else if #["combined-static-pending-old", "combined-static-pending-new", "combined-static-mismatched-oid-width", "combined-static-same-manifest-oids"].contains label then
    let (col, value) := if label.endsWith "pending-old" then (4, "PENDING") else if label.endsWith "pending-new" then (5, "PENDING")
      else if label.endsWith "mismatched-oid-width" then (5, String.ofList (List.replicate 64 'a')) else (5, ca[4]!)
    caChange col value
  else if #["combined-actual-content-unchanged", "combined-unchanged-content-integration"].contains label then
    change "claims.tsv" x 7 (← record before "claims.tsv" x)[7]!
  else if label == "combined-wrong-pending-old-manifest" then caChange 4 (String.ofList (List.replicate 40 'a'))
  else if label == "combined-wrong-fixed-old-record" then
    mutate before "claims.tsv" x 8 (String.ofList (List.replicate 40 'a'))
    refresh ctx before
  else if label == "combined-wrong-new-manifest" then caChange 5 (String.ofList (List.replicate 40 'a'))
  else if #["combined-wrong-current-new-record", "combined-pending-current-new-record"].contains label then
    change "claims.tsv" x 8 (if label.startsWith "combined-pending" then "PENDING" else String.ofList (List.replicate 40 'a'))
  else if label == "combined-newline-appended-new-hash" then
    let value ← blob ctx ((← record after "claims.tsv" x)[7]! ++ "\n")
    caChange 5 value
    change "claims.tsv" x 8 value
  else if label == "combined-newline-appended-old-hash" then caChange 4 (← blob ctx ((← record before "claims.tsv" x)[7]! ++ "\n"))
  else if label.startsWith "combined-contentless-" then
    let text := if label.endsWith "empty" then "" else if label.endsWith "true" then "True." else "False"
    change "claims.tsv" x 7 text
    change "claims.tsv" x 8 (← blob ctx text)
    caChange 5 (← blob ctx text)
  else if #["combined-static-wrong-page-pin", "combined-static-pending-page-pin"].contains label then
    caChange 6 (if label == "combined-static-pending-page-pin" then "PENDING" else String.ofList (List.replicate 40 'a'))
  else if label == "combined-base-page-pin-drift" then
    mutate before "pages.tsv" (← record before "claims.tsv" x)[3]! 9 (String.ofList (List.replicate 40 'a'))
  else if label == "combined-current-page-pin-drift" then
    change "pages.tsv" (← record after "claims.tsv" x)[3]! 9 (String.ofList (List.replicate 40 'a'))
    caChange 6 (String.ofList (List.replicate 40 'a'))
  else if label == "combined-current-page-record-drift" then change "pages.tsv" (← record after "claims.tsv" x)[3]! 5 "synthetic-section"
  else if #["combined-unrelated-source-drift", "combined-independent-second-source-control-t"].contains label then
    secondSource before
    secondSource after
    if label == "combined-unrelated-source-drift" then change "sources.tsv" "SRB" 5 "Changed synthetic title"
  else if label == "combined-page-identity-drift" then
    let currentPage := (← record after "claims.tsv" x)[3]!
    let page := ((← table after "pages.tsv").find? fun r => r[1]?.getD "" == "TASAKI2020" && r[0]?.getD "" != currentPage).get!
    change "claims.tsv" x 3 page[0]!
    caChange 6 page[9]!
  else if label.startsWith "combined-base-" || label.startsWith "combined-current-" then
    let base := label.startsWith "combined-base-"
    let what := label.replace (if base then "combined-base-" else "combined-current-") ""
    let target := if base then before else after
    let active := #[("excluded", 5, "out_of_scope"), ("tombstoned", 11, "true"), ("exclusion-rationale", 9, "UNEXPECTED"),
      ("exclusion-ref", 10, "UNEXPECTED"), ("successor", 12, "CL-SYNTHETIC-9999"),
      ("tombstone-rationale", 13, "UNEXPECTED"), ("tombstone-ref", 14, "UNEXPECTED")]
    if let some (_, col, value) := active.find? (fun entry => entry.1 == what) then mutate target "claims.tsv" x col value
    else if #["skeleton_frozen", "proof_active"].contains what then mutate target "source-progress.tsv" "TASAKI2020" 1 what
    else if what.startsWith "binding-" then add target "bindings.tsv" (← bindingRow target (if what == "binding-x" then x else other))
    else
      let (name, row) := if what == "slice" then ("slices.tsv", #["SL-RUNTIME-0001", "1", x])
        else if what == "dependency-out" then ("dependencies.tsv", #[x, "requires", other, "NONE"])
        else if what == "dependency-in" then ("dependencies.tsv", #[other, "consequence_of", x, "NONE"])
        else ("claim-axioms.tsv", #[x, "AX-PROJECT-0001"])
      add target name row
  else if label == "combined-unknown-frozen-claim" then remove before "claims.tsv" x
  else if label.startsWith "combined-new-" && label.endsWith "-artifact" then
    let name := (label.replace "combined-new-" "").replace "-artifact" "" ++ ".tsv"
    let row ← if name == "bindings.tsv" then do
        let binding ← bindingRow after other
        pure (binding.set! 0 "CL-FOREIGN-9999")
      else pure <| if name == "claim-context.tsv" then #[other, "1", x, "term_reference", "inherited", "FIXTURE"]
        else if name == "statement-modules.tsv" then #["LatticeSystem.Claims.Runtime", "LatticeSystem/Claims/Runtime.lean", "leaf"]
        else if name == "statement-imports.tsv" then #["LatticeSystem.Claims.Runtime", "1", "Mathlib.Init", "true", "false", "false"]
        else #["AX-PROJECT-9999", "LatticeSystem.Axioms.State.fixture", "LatticeSystem.Axioms.State", "state", "fixture", "fixture", "reopen", "PENDING"]
    add after name row
  else if label == "combined-vocabulary-missing-review" then remove after "claim-vocabulary-review.tsv" x
  else if label == "combined-vocabulary-duplicate-review" then add after "claim-vocabulary-review.tsv" (← record after "claim-vocabulary-review.tsv" x)
  else if label == "combined-vocabulary-add-use" then add after "claim-vocabulary.tsv" #[x, (← table after "vocabulary.tsv")[1]![0]!]
  else if #["combined-vocabulary-remove-use", "combined-vocabulary-alter-use"].contains label then
    let uses ← table after "claim-vocabulary.tsv"
    let indices := (List.range uses.size).filter fun i => i > 0 && uses[i]![0]! == x
    if label == "combined-vocabulary-remove-use" then
      writeTable after "claim-vocabulary.tsv" <| uses.extract 0 indices[0]! ++ uses.extract (indices[0]! + 1) uses.size
    else writeTable after "claim-vocabulary.tsv" <| uses.set! indices[0]! (uses[indices[0]!]!.set! 1 uses[indices[1]!]![1]!)
  else if label == "combined-vocabulary-declaration-drift" then
    let rows ← table after "vocabulary.tsv"
    let col := ((List.range rows[0]!.size).find? fun i => rows[0]![i]! == "design_role").get!
    change "vocabulary.tsv" rows[1]![0]! col "SYNTHETIC-CHANGED"
  else if label.startsWith "combined-static-forbidden-" then
    let name := label.replace "combined-static-forbidden-" "" ++ ".tsv"
    let row ← if name == "claim-successors.tsv" then do
        pure #[← unusedId after name "SE-RUNTIME", event, cc[0]!, x, "1", "new_successor", other]
      else pure #[← unusedId after name "IA-RUNTIME", event, cc[0]!, "1", "IT-RUNTIME-0001", ref]
    add after name row
  else if #["combined-new-unowned-claim", "combined-new-unowned-item"].contains label then
    let tmp := FilePath.mk (after.toString ++ "-omission")
    let om ← prepareOmission ctx after tmp
    let name := if label == "combined-new-unowned-claim" then "claims.tsv" else "source-items.tsv"
    let row ← record tmp name (if name == "claims.tsv" then om.claim else om.item)
    let rows ← table after name
    let index := ((List.range rows.size).find? fun i => i > 0 && rows[i]![2]! > row[2]!).get!
    writeTable after name <| rows.extract 0 index ++ #[row] ++ rows.extract index rows.size
    if name == "claims.tsv" then refresh ctx after
    ctx.owned tmp
    IO.FS.removeDirAll tmp
  else if label == "combined-existing-item-metadata" then
    let item := ((← table after "item-claims.tsv").find? fun r => r[2]?.getD "" == x).get![0]!
    change "source-items.tsv" item 7 "Synthetic changed locator"
  else if label == "combined-old-item-relation-delete" then remove after "item-claims.tsv" x 2
  else if label == "combined-new-target-item-relation" then
    let item := ((← table after "item-claims.tsv").find? fun r => r[2]?.getD "" == other).get![0]!
    add after "item-claims.tsv" #[item, "99", x]
  else if label.startsWith "combined-invariant-" then
    let suffix := label.replace "combined-invariant-" ""
    let col := if suffix == "active-count" then 2 else if suffix == "target-count" then 3
      else if suffix == "equation-count" then 4 else if suffix == "no-claim-pages" then 5 else 6
    let invariant ← record after "source-invariants.tsv" "TASAKI2020"
    let value := if col == 6 then String.ofList (List.replicate 40 'a')
      else toString (invariant[col]!.toNat! + 1)
    change "source-invariants.tsv" "TASAKI2020" col value
  else if label == "history-later-lifecycle-static-only-s" then change "source-progress.tsv" "TASAKI2020" 1 "skeleton_frozen"
  else if label == "history-stale-next-old-oid" then
    let first := ((← table after "claim-content-amendments.tsv").find? fun r => r[3]?.getD "" == x).get!
    caChange 4 first[4]!
  else if label == "history-second-event-wrong-old-class" then
    change "claim-corrections.tsv" cc[0]! 6 "domain"
    change "claim-corrections.tsv" cc[0]! 7 "domain"
  else if label == "history-same-event-second-owner" then
    let previous := ((← table after "claim-content-amendments.tsv").find? fun r => r[3]?.getD "" == x && r[1]?.getD "" != event).get!
    let oldEvent := previous[1]!
    let oldRef := (← record after "correction-events.tsv" oldEvent)[4]!
    for (name, id) in #[("claim-normalization-reviews.tsv", nr), ("claim-corrections.tsv", cc[0]!)] do
      change name id 1 oldEvent
      change name id 2 "2"
    change "claim-normalization-reviews.tsv" nr 8 oldRef
    caChange 1 oldEvent
    caChange 7 oldRef
  else if label == "history-foreign-new-ca-event" then
    let tmp := FilePath.mk (after.toString ++ "-foreign")
    discard <| contentEvent ctx after tmp other
    for name in historyTables ++ #["claims.tsv", "claim-vocabulary-review.tsv", "source-invariants.tsv"] do
      IO.FS.writeFile (after / "registry" / name) (← IO.FS.readFile (tmp / "registry" / name))
    ctx.owned tmp
    IO.FS.removeDirAll tmp
  else if label.startsWith "history-prefix-reorder-" || label == "history-helper-ca-prefix-reorder" then
    let name := if label == "history-helper-ca-prefix-reorder" then "claim-content-amendments.tsv"
      else label.replace "history-prefix-reorder-" "" ++ ".tsv"
    let rows ← table after name
    let key := if name == "claim-successors.tsv" then 2 else 1
    let groups := (rows.extract 1 rows.size).foldl (fun groups row =>
      let groups := if groups.isEmpty || groups.back![0]![key]! != row[key]! then groups.push #[] else groups
      groups.set! (groups.size - 1) (groups.back!.push row)) (#[] : Array (Array (Array String)))
    ensure (groups.size >= 2) "two historical event groups"
    let groups := (groups.set! 0 groups[1]!).set! 1 groups[0]!
    writeTable after name <| #[rows[0]!] ++ groups.flatten
  else if label == "history-event-physical-reorder" then
    let rows ← table after "correction-events.tsv"
    writeTable after "correction-events.tsv" <| (rows.set! 1 rows[2]!).set! 2 rows[1]!
  else if label.startsWith "history-old-value-" then
    let name := label.replace "history-old-value-" "" ++ ".tsv"
    let row := (← table after name)[1]!
    let (col, value) := if name == "correction-events.tsv" then (4, "CHANGED-REVIEW")
      else if name == "claim-normalization-reviews.tsv" then (7, "exact-statement-ready-RUNTIME-HISTORY-MUTANT")
      else if name == "claim-corrections.tsv" then (9, "lemma")
      else if name == "claim-successors.tsv" then (6, other)
      else if name == "source-item-additions.tsv" then (5, "CORPUS-NORMALIZATION-INDEPENDENT-REVIEW-RUNTIME-HISTORY-MUTANT")
      else (7, "SOURCE-FIDELITY-TASAKI2020-0478-INDEPENDENT-REVIEW-V1-RUNTIME-HISTORY-MUTANT")
    let frozen := #[("claim-normalization-reviews.tsv", "NR-TASAKI2020-0001", "exact-statement-ready"),
      ("claim-corrections.tsv", "CC-TASAKI2020-0001", "remark"),
      ("source-item-additions.tsv", "IA-TASAKI2020-0001", "CORPUS-NORMALIZATION-INDEPENDENT-REVIEW"),
      ("claim-content-amendments.tsv", "CA-TASAKI2020-0001", "SOURCE-FIDELITY-TASAKI2020-0478-INDEPENDENT-REVIEW-V1")]
    for (file, id, expected) in frozen do
      if file == name then ensure (row[0]! == id && row[col]! == expected) "known historical control row"
    ensure (row[col]! != value) "historical mutant changes bytes"
    change name row[0]! col value
  else if label == "combined-ordinary-rejects-full-diff" then pure ()
  else if #["history-reopen-old-event-class-content", "selector-real-historical-reopen"].contains label then
    change "claims.tsv" x 5 "notation"
    change "claims.tsv" x 6 "notation"
    let text := "Synthetic historical reopen"
    change "claims.tsv" x 7 text
    change "claims.tsv" x 8 (← blob ctx text)
    refresh ctx after
  else if label == "history-ordinary-ca-piggyback" then
    add after "claim-content-amendments.tsv" (ca.set! 0 (← unusedId after "claim-content-amendments.tsv" "CA-PIGGYBACK"))
  else if label == "none-old-combined-static" then
    change "claim-corrections.tsv" cc[0]! 6 "NONE"
    change "claim-corrections.tsv" cc[0]! 7 "NONE"
  else throw <| IO.userError ("unimplemented mutant " ++ label)
/-- The independently inventoried combined-correction case metadata used by execution. -/
def combinedCases : Array (String × String × String × Bool × String) := #[
  ("combined-fixed-s", "F", "S", true, "check-content-amendments: ok"),
  ("combined-fixed-h", "F", "H", true, "check-content-amendments: ok"),
  ("combined-fixed-t", "F", "T", true, "check-claim-corrections: ok"),
  ("combined-fixed-b", "F", "B", true, "check-base-diff: ok"),
  ("combined-fixed-c", "F", "C", true, "check-registry: ok"),
  ("combined-pending-h", "P", "H", true, "check-content-amendments: ok"),
  ("combined-pending-t", "P", "T", true, "check-claim-corrections: ok"),
  ("combined-pending-b", "P", "B", true, "check-base-diff: ok"),
  ("combined-disposition-only-h", "D", "H", true, "check-content-amendments: ok"),
  ("combined-disposition-only-t", "D", "T", true, "check-claim-corrections: ok"),
  ("combined-subkind-only-h", "K", "H", true, "check-content-amendments: ok"),
  ("combined-subkind-only-t", "K", "T", true, "check-claim-corrections: ok"),
  ("combined-project-vocabulary-h", "V", "H", true, "check-content-amendments: ok"),
  ("combined-project-vocabulary-t", "V", "T", true, "check-claim-corrections: ok"),
  ("combined-legacy-no-ca-header-s", "N", "S", true, "check-content-amendments: ok"),
  ("combined-legacy-no-ca-header-h", "N", "H", true, "check-content-amendments: ok"),
  ("combined-legacy-no-ca-header-t", "N", "T", true, "check-claim-corrections: ok"),
  ("combined-independent-omission-nested-insert-h", "M", "H", true, "check-content-amendments: ok"),
  ("combined-independent-omission-nested-insert-t", "M", "T", true, "check-claim-corrections: ok"),
  ("combined-independent-omission-nested-insert-b", "M", "B", true, "check-base-diff: ok"),
  ("combined-independent-omission-nested-insert-i", "M", "I", true, "check-source-items: ok"),
  ("combined-target-vocab-row-order-preserved-set-h", "W", "H", true, "check-content-amendments: ok"),
  ("combined-target-vocab-row-order-preserved-set-t", "W", "T", true, "check-claim-corrections: ok"),
  ("combined-unknown-outcome", "F", "T", false, "invalid claim normalization review ledger"),
  ("combined-unknown-action", "F", "T", false, "invalid claim correction ledger"),
  ("combined-open-review", "F", "T", false, "invalid claim normalization review ledger"),
  ("combined-wrong-scope", "F", "T", false, "invalid claim normalization review ledger"),
  ("combined-wrong-outcome", "F", "T", false, "invalid claim correction ledger"),
  ("combined-static-missing-ca", "F", "S", false, "content amendment is missing its provenance row"),
  ("combined-static-duplicate-ca", "F", "S", false, "duplicate content amendment"),
  ("combined-static-duplicate-owner-nr", "F", "S", false, "combined correction lacks exactly one owning review and correction"),
  ("combined-static-duplicate-owner-cc", "F", "S", false, "combined correction lacks exactly one owning review and correction"),
  ("combined-static-mixed-owner", "F", "S", false, "combined correction lacks exactly one owning review and correction"),
  ("combined-static-ca-wrong-event", "F", "S", false, "content amendment event or correction ownership mismatch"),
  ("combined-static-ca-wrong-correction", "F", "S", false, "content amendment event or correction ownership mismatch"),
  ("combined-static-ca-wrong-claim", "F", "S", false, "content amendment event or correction ownership mismatch"),
  ("combined-static-ca-wrong-review", "F", "S", false, "content amendment review ownership mismatch"),
  ("combined-static-nr-wrong-outcome", "F", "S", false, "content amendment review ownership mismatch"),
  ("combined-static-nr-wrong-scope", "F", "S", false, "content amendment review ownership mismatch"),
  ("combined-static-nr-open", "F", "S", false, "content amendment review ownership mismatch"),
  ("combined-static-event-wrong-source", "F", "S", false, "content amendment source mismatch"),
  ("combined-static-ca-owned-reclassify", "F", "S", false, "content amendment event or correction ownership mismatch"),
  ("combined-static-ca-owned-split", "F", "S", false, "content amendment event or correction ownership mismatch"),
  ("combined-static-ca-owned-add_omitted_claim", "F", "S", false, "content amendment event or correction ownership mismatch"),
  ("combined-duplicate-owner-integration", "F", "T", false, "invalid claim normalization review ledger"),
  ("combined-missing-ca-integration", "F", "T", false, "content amendment is missing its provenance row"),
  ("combined-class-pair-no-op-s", "F", "S", false, "combined correction requires changed classification"),
  ("combined-class-pair-no-op-h", "F", "H", false, "combined correction requires changed classification"),
  ("combined-wrong-old-disposition-h", "F", "H", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-old-disposition-t", "F", "T", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-old-subkind-h", "F", "H", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-old-subkind-t", "F", "T", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-new-disposition-h", "F", "H", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-new-disposition-t", "F", "T", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-new-subkind-h", "F", "H", false, "combined correction classification does not match claim transition"),
  ("combined-wrong-new-subkind-t", "F", "T", false, "combined correction classification does not match claim transition"),
  ("combined-static-none-old-disposition", "F", "S", false, "combined correction has invalid classification"),
  ("combined-static-none-old-subkind", "F", "S", false, "combined correction has invalid classification"),
  ("combined-static-old-out-of-scope", "F", "S", false, "combined correction has invalid classification"),
  ("combined-static-new-out-of-scope", "F", "S", false, "combined correction has invalid classification"),
  ("combined-static-illegal-new-kind", "F", "S", false, "combined correction has invalid classification"),
  ("combined-static-illegal-new-subkind", "F", "S", false, "combined correction has invalid classification"),
  ("legacy-amend-class-drift-static", "A", "S", false, "content amendment changes classification"),
  ("legacy-amend-actual-class-drift-helper", "A", "H", false, "content amendment changed frozen claim identity or metadata"),
  ("legacy-reclass-content-drift", "Q", "T", false, "unmanifested claim drift"),
  ("combined-static-pending-old", "F", "S", false, "content amendment requires frozen old and new content OIDs"),
  ("combined-static-pending-new", "F", "S", false, "content amendment requires frozen old and new content OIDs"),
  ("combined-static-mismatched-oid-width", "F", "S", false, "content amendment requires frozen old and new content OIDs"),
  ("combined-static-same-manifest-oids", "F", "S", false, "content amendment is a no-op"),
  ("combined-actual-content-unchanged", "F", "H", false, "content amendment is a no-op"),
  ("combined-wrong-pending-old-manifest", "P", "H", false, "content amendment old content OID is stale"),
  ("combined-wrong-fixed-old-record", "F", "H", false, "content amendment old content OID is stale"),
  ("combined-wrong-new-manifest", "F", "H", false, "content amendment new content OID is stale"),
  ("combined-wrong-current-new-record", "F", "H", false, "content amendment new content OID is stale"),
  ("combined-pending-current-new-record", "F", "H", false, "content amendment new content OID is stale"),
  ("combined-newline-appended-new-hash", "F", "H", false, "content amendment new content OID is stale"),
  ("combined-newline-appended-old-hash", "P", "H", false, "content amendment old content OID is stale"),
  ("combined-contentless-empty", "F", "H", false, "contentless content amendment surrogate"),
  ("combined-contentless-true", "F", "H", false, "contentless content amendment surrogate"),
  ("combined-contentless-false", "F", "H", false, "contentless content amendment surrogate"),
  ("combined-unchanged-content-integration", "F", "T", false, "content amendment is a no-op"),
  ("combined-static-wrong-page-pin", "F", "S", false, "content amendment page source mismatch"),
  ("combined-static-pending-page-pin", "F", "S", false, "content amendment page source mismatch"),
  ("combined-base-page-pin-drift", "F", "H", false, "content amendment page source mismatch"),
  ("combined-current-page-pin-drift", "F", "H", false, "content amendment page source mismatch"),
  ("combined-current-page-record-drift", "F", "H", false, "combined correction page record changed"),
  ("combined-source-pin-drift", "F", "H", false, "combined correction source record changed or is not frozen"),
  ("combined-unrelated-source-drift", "F", "T", false, "unrelated frozen registry drift"),
  ("combined-independent-second-source-control-t", "F", "T", true, "check-claim-corrections: ok"),
  ("combined-frozen-order", "F", "H", false, "combined correction changed frozen claim identity or metadata"),
  ("combined-frozen-locator", "F", "H", false, "combined correction changed frozen claim identity or metadata"),
  ("combined-source-identity-drift", "F", "H", false, "content amendment source mismatch"),
  ("combined-page-identity-drift", "F", "H", false, "combined correction changed frozen claim identity or metadata"),
  ("combined-base-excluded", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-base-tombstoned", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-base-exclusion-rationale", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-base-exclusion-ref", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-base-successor", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-base-tombstone-rationale", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-base-tombstone-ref", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-excluded", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-tombstoned", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-exclusion-rationale", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-exclusion-ref", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-successor", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-tombstone-rationale", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-current-tombstone-ref", "F", "H", false, "combined correction requires an active formalization target"),
  ("combined-unknown-frozen-claim", "F", "H", false, "content amendment does not target a frozen source claim"),
  ("combined-base-skeleton_frozen", "F", "H", false, "content amendment requires a pre-R4 source"),
  ("combined-base-proof_active", "F", "H", false, "content amendment requires a pre-R4 source"),
  ("combined-base-binding-x", "F", "H", false, "content amendment source already has bindings"),
  ("combined-base-binding-other_same_source", "F", "H", false, "content amendment source already has bindings"),
  ("combined-base-slice", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-base-dependency-out", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-base-dependency-in", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-base-claim-axiom", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-current-skeleton_frozen", "F", "H", false, "content amendment requires a pre-R4 source"),
  ("combined-current-proof_active", "F", "H", false, "content amendment requires a pre-R4 source"),
  ("combined-current-binding-x", "F", "H", false, "content amendment source already has bindings"),
  ("combined-current-binding-other_same_source", "F", "H", false, "content amendment source already has bindings"),
  ("combined-current-slice", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-current-dependency-out", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-current-dependency-in", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-current-claim-axiom", "F", "H", false, "content amendment target already has skeleton or axiom relations"),
  ("combined-new-bindings-artifact", "F", "T", false, "correction event introduces an R4 artifact"),
  ("combined-new-claim-context-artifact", "F", "T", false, "correction event introduces an R4 artifact"),
  ("combined-new-statement-modules-artifact", "F", "T", false, "correction event introduces an R4 artifact"),
  ("combined-new-statement-imports-artifact", "F", "T", false, "correction event introduces an R4 artifact"),
  ("combined-new-axioms-artifact", "F", "T", false, "correction event introduces an axiom artifact"),
  ("combined-vocabulary-basis-drift", "F", "H", false, "content amendment lacks its refreshed vocabulary review"),
  ("combined-vocabulary-stale-ref", "F", "H", false, "content amendment lacks its refreshed vocabulary review"),
  ("combined-vocabulary-missing-review", "F", "H", false, "content amendment lacks its refreshed vocabulary review"),
  ("combined-vocabulary-duplicate-review", "F", "H", false, "content amendment lacks its refreshed vocabulary review"),
  ("combined-vocabulary-add-use", "F", "H", false, "content amendment changed vocabulary use"),
  ("combined-vocabulary-remove-use", "V", "H", false, "content amendment changed vocabulary use"),
  ("combined-vocabulary-alter-use", "V", "H", false, "content amendment changed vocabulary use"),
  ("combined-unrelated-vocabulary-review", "F", "T", false, "unrelated vocabulary review drift"),
  ("combined-vocabulary-declaration-drift", "F", "T", false, "unrelated frozen registry drift"),
  ("combined-static-forbidden-claim-successors", "F", "S", false, "content amendment cannot introduce successors or source items"),
  ("combined-static-forbidden-source-item-additions", "F", "S", false, "content amendment cannot introduce successors or source items"),
  ("combined-new-unowned-claim", "F", "T", false, "split successor provenance is incomplete"),
  ("combined-new-unowned-item", "F", "T", false, "unmanifested source item addition"),
  ("combined-existing-item-metadata", "F", "T", false, "historical source item drift"),
  ("combined-old-item-relation-delete", "F", "T", false, "historical source item relation drift"),
  ("combined-new-target-item-relation", "F", "T", false, "unrelated item-claim drift"),
  ("combined-invariant-active-count", "F", "T", false, "census invariant count is stale"),
  ("combined-invariant-target-count", "F", "T", false, "formalization target count is stale"),
  ("combined-invariant-equation-count", "F", "T", false, "census invariant count is stale"),
  ("combined-invariant-no-claim-pages", "F", "T", false, "census invariant count is stale"),
  ("combined-invariant-census-oid", "F", "T", false, "census OID is stale"),
  ("combined-invariant-review", "F", "H", false, "combined correction lacks its event invariant review"),
  ("history-combined-then-combined-t", "CC", "T", true, "check-claim-corrections: ok"),
  ("history-combined-then-combined-b", "CC", "B", true, "check-base-diff: ok"),
  ("history-combined-then-combined-s", "CC", "S", true, "check-content-amendments: ok"),
  ("history-combined-then-combined-o", "CC", "O", true, "check-base-diff: ok"),
  ("history-combined-then-amend-t", "CA", "T", true, "check-claim-corrections: ok"),
  ("history-combined-then-amend-b", "CA", "B", true, "check-base-diff: ok"),
  ("history-combined-then-amend-s", "CA", "S", true, "check-content-amendments: ok"),
  ("history-combined-then-amend-o", "CA", "O", true, "check-base-diff: ok"),
  ("history-amend-then-combined-t", "AC", "T", true, "check-claim-corrections: ok"),
  ("history-amend-then-combined-b", "AC", "B", true, "check-base-diff: ok"),
  ("history-amend-then-combined-s", "AC", "S", true, "check-content-amendments: ok"),
  ("history-amend-then-combined-o", "AC", "O", true, "check-base-diff: ok"),
  ("history-combined-reclass-amend-t", "CRAC", "T", true, "check-claim-corrections: ok"),
  ("history-combined-reclass-amend-b", "CRAC", "B", true, "check-base-diff: ok"),
  ("history-combined-reclass-amend-s", "CRAC", "S", true, "check-content-amendments: ok"),
  ("history-combined-reclass-amend-o", "CRAC", "O", true, "check-base-diff: ok"),
  ("history-omission-then-combined-t", "OC", "T", true, "check-claim-corrections: ok"),
  ("history-omission-then-combined-b", "OC", "B", true, "check-base-diff: ok"),
  ("history-omission-then-combined-s", "OC", "S", true, "check-content-amendments: ok"),
  ("history-omission-then-combined-o", "OC", "O", true, "check-base-diff: ok"),
  ("history-combined-then-split-t", "CS", "T", true, "check-claim-corrections: ok"),
  ("history-combined-then-split-b", "CS", "B", true, "check-base-diff: ok"),
  ("history-combined-then-split-s", "CS", "S", true, "check-content-amendments: ok"),
  ("history-combined-then-split-o", "CS", "O", true, "check-base-diff: ok"),
  ("history-combined-then-exclude-t", "CX", "T", true, "check-claim-corrections: ok"),
  ("history-combined-then-exclude-b", "CX", "B", true, "check-base-diff: ok"),
  ("history-combined-then-exclude-s", "CX", "S", true, "check-content-amendments: ok"),
  ("history-combined-then-exclude-o", "CX", "O", true, "check-base-diff: ok"),
  ("history-intervening-pure-reclassification-t", "CRAC", "T", true, "check-claim-corrections: ok"),
  ("history-later-lifecycle-static-only-s", "CC", "S", true, "check-content-amendments: ok"),
  ("history-stale-next-old-oid", "CC", "S", false, "content amendment history chain is stale"),
  ("history-second-event-wrong-old-class", "CC", "H", false, "combined correction classification does not match claim transition"),
  ("history-same-event-second-owner", "CC", "S", false, "combined correction lacks exactly one owning review and correction"),
  ("history-foreign-new-ca-event", "F", "H", false, "content amendment belongs to another event"),
  ("history-prefix-reorder-claim-normalization-reviews", "HIST", "T", false, "historical correction ledger drift"),
  ("history-prefix-reorder-claim-corrections", "HIST", "T", false, "historical correction ledger drift"),
  ("history-prefix-reorder-claim-successors", "HIST", "T", false, "historical correction ledger drift"),
  ("history-prefix-reorder-source-item-additions", "HIST", "T", false, "historical correction ledger drift"),
  ("history-prefix-reorder-claim-content-amendments", "HIST", "T", false, "historical correction ledger drift"),
  ("history-event-physical-reorder", "HIST", "T", false, "invalid correction event ledger"),
  ("history-helper-ca-prefix-reorder", "HIST", "H", false, "historical content amendment drift"),
  ("history-old-value-correction-events", "HIST", "T", false, "historical correction ledger drift"),
  ("history-old-value-claim-normalization-reviews", "HIST", "T", false, "historical correction ledger drift"),
  ("history-old-value-claim-corrections", "HIST", "T", false, "historical correction ledger drift"),
  ("history-old-value-claim-successors", "HIST", "T", false, "historical correction ledger drift"),
  ("history-old-value-source-item-additions", "HIST", "T", false, "unmanifested source item addition"),
  ("history-old-value-claim-content-amendments", "HIST", "T", false, "historical correction ledger drift"),
  ("combined-ordinary-rejects-full-diff", "F", "O", false, "identity/order/locator/content/exclusion/supersession"),
  ("history-reopen-old-event-class-content", "CC", "E", false, "identity/order/locator/content/exclusion/supersession"),
  ("history-ordinary-ca-piggyback", "CC", "O", false, "historical correction ledger drift"),
  ("selector-real-first-combined", "J", "R", true, "check-base-diff: ok"),
  ("selector-real-second-combined", "J", "R", true, "check-base-diff: ok"),
  ("selector-real-historical-ordinary", "J", "R", true, "check-base-diff: ok"),
  ("selector-real-wrong-base", "J", "R", false, "new correction event base commit does not match the actual merge base"),
  ("selector-real-two-new-events", "J", "R", false, "multiple new correction events require an explicit CI policy change"),
  ("selector-real-invalid-base", "J", "R", false, "invalid or unfetched base ref"),
  ("selector-real-class-fact-mutant", "J", "R", false, "combined correction classification does not match claim transition"),
  ("selector-real-historical-reopen", "J", "R", false, "identity/order/locator/content/exclusion/supersession"),
  ("none-old-combined-static", "F", "S", false, "combined correction has invalid classification"),
  ("none-old-combined-new-id-transition", "F", "T", false, "correction predecessor source mismatch"),
  ("combined-generator-privacy", "PUBLIC", "G", true, "combined generator privacy contract: ok"),
]


/-- Run one real Git-to-selector-to-transition chain without executable substitutions. -/
def runSelector (ctx : Context) (cache : FixtureCache) (legacy : FilePath)
    (label : String) (positive : Bool) (diagnostic : String) : IO Unit := do
  ensure ((← IO.getEnv "CHECK_BASE_DIFF").isNone) "selector must use the actual base checker"
  let repo := ctx.temporary / label
  IO.FS.createDirAll repo
  ctx.owned repo
  let git := fun args => Checker.TestSupport.git repo args
  discard <| git #["init", "-q"]
  discard <| git #["config", "user.name", "phasetr"]
  discard <| git #["config", "user.email", "phasetr@gmail.com"]
  discard <| git #["commit", "--allow-empty", "-qm", "Synthetic selector seed"]
  let seed := (← git #["rev-parse", "HEAD"]).trimAscii.toString
  let f ← fixture ctx cache legacy "F"
  installRegistry ctx f.before repo
  discard <| git #["add", "registry"]
  discard <| git #["commit", "-qm", "Synthetic selector base"]
  let b0 := (← git #["rev-parse", "HEAD"]).trimAscii.toString
  let snapshot := FilePath.mk (repo.toString ++ "-b0")
  copyRegistry ctx repo snapshot
  let e1 := FilePath.mk (repo.toString ++ "-e1")
  let e1Event ← contentEvent ctx snapshot e1 claim (some ("definition", "definition"))
  mutate e1 "correction-events.tsv" e1Event 3 b0
  installRegistry ctx e1 repo
  let baseRef ← if #["selector-real-second-combined", "selector-real-historical-ordinary", "selector-real-two-new-events", "selector-real-historical-reopen"].contains label then do
    assertContentStep ctx snapshot e1 e1Event
    discard <| git #["add", "registry"]
    discard <| git #["commit", "-qm", "Synthetic first combined event"]
    let e1Sha := (← git #["rev-parse", "HEAD"]).trimAscii.toString
    let e2 := FilePath.mk (repo.toString ++ "-e2")
    let e2Event ← contentEvent ctx e1 e2 claim (some ("assertion", "equation"))
    mutate e2 "correction-events.tsv" e2Event 3 e1Sha
    installRegistry ctx e2 repo
    assertContentStep ctx e1 e2 e2Event
    let baseRef := if label == "selector-real-two-new-events" then b0 else e1Sha
    if #["selector-real-historical-ordinary", "selector-real-historical-reopen"].contains label then do
      discard <| git #["add", "registry"]
      discard <| git #["commit", "-qm", "Synthetic second combined event"]
      let baseRef := (← git #["rev-parse", "HEAD"]).trimAscii.toString
      if label.endsWith "reopen" then mutateCombined ctx label e2 repo e2Event claim
      pure baseRef
    else pure baseRef
    else if label == "selector-real-wrong-base" then do
      mutate repo "correction-events.tsv" e1Event 3 seed
      pure b0
    else if label == "selector-real-invalid-base" then pure "refs/heads/does-not-exist"
    else if label == "selector-real-class-fact-mutant" then do
      let cc := ((← table repo "claim-corrections.tsv").find? fun r => r[1]?.getD "" == e1Event).get!
      mutate repo "claim-corrections.tsv" cc[0]! 6 "domain"
      pure b0
    else do
      assertContentStep ctx snapshot repo e1Event
      pure b0
  let output ← expect ctx label positive
    (ctx.command "base-diff-ci" #[repo.toString, baseRef]) diagnostic
  if positive then
    ensure ((output.splitOn "check-base-diff: ok").length > 1) "selector executed actual base diff"
    ensure (((output.splitOn "check-base-diff-ci: ok").length > 1) ==
      (label != "selector-real-historical-ordinary")) "selector chose current or historical route"
  for suffix in #["-b0", "-e1", "-e2"] do
    let path := FilePath.mk (repo.toString ++ suffix)
    if ← path.pathExists then
      ctx.owned path
      IO.FS.removeDirAll path

/-- Check combined repairs' exact public classification, item identity and private-byte exclusion. -/
def combinedPublic (ctx : Context) (before after : FilePath) (event x : String) : IO Unit := do
  generate ctx after
  let value ← catalog after
  let itemId := ((← table after "item-claims.tsv").find? fun r => r[2]?.getD "" == x).get![0]!
  let item ← catalogItem value itemId
  let claims ← jsonArray (← property item "claims")
  let rendered ← claims.foldlM (fun rendered member => do
    pure (if (← jsonString (← property member "claim_id")) == x then member else rendered)) Json.null
  ensure ((← jsonString (← property rendered "disposition")) == "definition" &&
    (← jsonString (← property rendered "subkind")) == "definition") "combined public classification"
  let original ← record before "source-items.tsv" itemId
  ensure ((← jsonString (← property item "public_group")) == original[8]! &&
    (← jsonString (← property item "public_slug")) == original[9]!) "combined public grouping"
  for name in #["source-items.tsv", "item-claims.tsv"] do
    ensure ((← table before name) == (← table after name)) "combined public original provenance"
  let text ← publicText (after / "docs")
  let row ← record after "claims.tsv" x
  let cc := ((← table after "claim-corrections.tsv").find? fun r => r[1]?.getD "" == event).get!
  let ca := ((← table after "claim-content-amendments.tsv").find? fun r => r[2]?.getD "" == cc[0]!).get!
  for token in #["PRIVATE-COMBINED", (← record before "claims.tsv" x)[7]!, row[7]!,
      ca[4]!, ca[5]!, event, cc[0]!, cc[3]!, ca[0]!, ca[7]!] do
    ensure ((text.splitOn token).length == 1) "private combined bytes in public output"
  generate ctx after "--check"
  assertContentStep ctx before after event

/-- Execute the combined matrix against native routes and actual renderer/selector entrypoints. -/
def combined (ctx : Context) (legacy : FilePath) : IO Unit := do
  ensure (combinedCases.size == 212 &&
    (combinedCases.filter fun (_, _, _, positive, _) => positive).size == 58) "combined case inventory"
  let cache ← IO.mkRef #[]
  let startAccepted ← ctx.accepted.get
  let startRejected ← ctx.rejected.get
  for (label, kind, route, positive, diagnostic) in combinedCases do
    if route == "R" then runSelector ctx cache legacy label positive diagnostic
    else
      let source ← fixture ctx cache legacy (if kind == "PUBLIC" then "F" else kind)
      let source ← if label == "history-intervening-pure-reclassification-t" then do
        match (← cache.get).find? (fun entry => entry.1 == "CRAC-middle") with
        | some (_, middle) => pure middle
        | none => throw <| IO.userError ("missing historical fixture for " ++ label)
        else pure source
      let caseRoot := ctx.temporary / ("combined-case-" ++ label)
      IO.FS.createDirAll caseRoot
      let before := caseRoot / "base"
      let after := caseRoot / "current"
      copyFixture ctx (if #["O", "E"].contains route && label != "combined-ordinary-rejects-full-diff" then source.after else source.before) before
      copyFixture ctx source.after after
      let (event,x) ← if label == "none-old-combined-new-id-transition" then do
        ctx.owned after
        IO.FS.removeDirAll after
        let om ← prepareOmission ctx before after
        let event := om.event
        let x := om.claim
        mutate after "claim-normalization-reviews.tsv" om.normalization 5 "amend_and_reclassify"
        mutate after "claim-corrections.tsv" om.correction 5 "amend_and_reclassify"
        let row ← record after "claims.tsv" x
        add after "claim-content-amendments.tsv" #[← unusedId after "claim-content-amendments.tsv" "CA-RUNTIME",
          event, om.correction, x, ← blob ctx "Synthetic prior bytes", row[8]!,
          (← record after "pages.tsv" row[3]!)[9]!, om.review]
        pure (event,x)
        else do
          if !positive || #["combined-independent-second-source-control-t", "history-later-lifecycle-static-only-s"].contains label then
            mutateCombined ctx label before after source.event source.target
          pure (source.event,source.target)
      if positive && !#["O", "G"].contains route && label != "history-later-lifecycle-static-only-s" then
        assertContentStep ctx before after event
      if route == "G" then expectAction ctx label true (combinedPublic ctx before after event x)
      else
        let command := if route == "S" then ctx.content #["--static", after.toString]
          else if route == "H" then ctx.content #["--transition", before.toString, after.toString, event]
          else if route == "T" then ctx.command "corrections" #["--fixture-dirs", before.toString, after.toString]
          else if #["B", "E"].contains route then ctx.command "base-diff" #["--correction-event", event, "--fixture-dirs", before.toString, after.toString]
          else if route == "O" then ctx.command "base-diff" #["--fixture-dirs", before.toString, after.toString]
          else ctx.gate (if route == "C" then "registry" else "source-items") after
        discard <| expect ctx label positive command diagnostic
      ctx.owned caseRoot
      IO.FS.removeDirAll caseRoot
  ensure ((← ctx.accepted.get) - startAccepted == 58 && (← ctx.rejected.get) - startRejected == 154)
    "combined execution inventory differs from 58 positive and 154 rejection cases"

/-- Run all content-amendment, omission, shared-item and combined-correction regressions. -/
def run (ctx : Context) : IO Unit := do
  let accepted ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let base := ctx.temporary / "base"
  copyRegistry ctx ctx.project base
  mutate base "claims.tsv" claim 8 "PENDING"
  refresh ctx base
  let current := ctx.temporary / "current"
  let am ← prepareAmendment ctx base current "For every admissible x, F(x) = G(x)."
  transition ctx "pending-old-content-event" base current
  let omitted := ctx.temporary / "omitted-claim"
  let om ← prepareOmission ctx base omitted
  let grouped := ctx.temporary / "grouped-omissions"
  let gr ← prepareGrouped ctx base grouped
  let legacy ← initial ctx base current am omitted om grouped gr
  ensure ((← ctx.accepted.get) - accepted == 49 && (← ctx.rejected.get) - rejected == 132)
    "initial content matrix differs from 49 positive and 132 rejection cases"
  combined ctx legacy
  ensure ((← ctx.accepted.get) - accepted == 107 && (← ctx.rejected.get) - rejected == 286)
    "content inventory differs from 393 cases (107 positive, 286 rejection)"
  IO.println "test-content-amendments-runtime: ok (393 cases; 107 positive, 286 rejection cases)"

end Checker.Tests.Content
