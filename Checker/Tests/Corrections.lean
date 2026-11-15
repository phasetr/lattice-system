import Checker.Tests.FixtureSupport

/-! Transition regressions for reviewed classifications, source-item additions and duplicate retirement. -/

namespace Checker.Tests.Corrections

open System Lean Checker.TestSupport Checker.Tests.FixtureSupport

/-- Invoke one dedicated transition with its original case label and one counted outcome. -/
def transition (ctx : Context) (label : String) (before after : FilePath)
    (positive : Bool := true) (diagnostic : String := "") : IO Unit := do
  discard <| expect ctx label positive
    (ctx.command "corrections" #["--fixture-dirs", before.toString, after.toString]) diagnostic

/-- Invoke one ordinary or event-owned base comparison with its own counted outcome. -/
def baseDiff (ctx : Context) (label : String) (before after : FilePath)
    (positive : Bool := true) (event : String := "") (diagnostic : String := "") : IO Unit := do
  let options := if event.isEmpty then #[] else #["--correction-event", event]
  discard <| expect ctx label positive (ctx.command "base-diff"
    (options ++ #["--fixture-dirs", before.toString, after.toString])) diagnostic

/-- The event used by the original production-derived correction cases. -/
def shellEvent : String := "RUNTIME-CORRECTION-EVENT-2"

/-- The exact historical source-correction base in the rewrite graph. -/
def baseCommit : String := "c6fb1ec6046626e14dd9a65f396a66386fcb9b7b"

/-- The first historical source-correction current tree. -/
def eventOneCommit : String := "cf4a289e7c766554c8821e167eddac2c3e291c2a"

/-- The independently reviewed token used by the production-derived fixtures. -/
def shellReview : String := "CORPUS-NORMALIZATION-TASAKI2020-2026-REVIEW"

/-- Capture exact relative file identities and bytes for an immutable-baseline oracle. -/
partial def snapshot (root : FilePath) (relativePrefix : String := "") : IO (Array (String × ByteArray)) := do
  let entries := (← root.readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut result := #[]
  for entry in entries do
    let relative := relativePrefix ++ entry.fileName
    if ← entry.path.isDir then result := result ++ (← snapshot entry.path (relative ++ "/"))
    else result := result.push (relative, ← IO.FS.readBinFile entry.path)
  pure result

/-- Clone only registry bytes, matching the original shell fixture's copy boundary. -/
def shellClone (ctx : Context) (before : FilePath) (name : String) : IO FilePath := do
  let target := ctx.temporary / "cases" / name
  copyRegistry ctx before target
  pure target

/-- Append the reviewed event to a fresh registry fixture. -/
def prepareEvent (ctx : Context) (before : FilePath) (name : String)
    (source : String := "TASAKI2020") : IO FilePath := do
  let target ← shellClone ctx before name
  add target "correction-events.tsv" #[shellEvent, toString (← table target "correction-events.tsv").size,
    source, baseCommit, shellReview]
  pure target

/-- Produce a minimal classification-only correction with its refreshed vocabulary review. -/
def makeReclassify (ctx : Context) (base : FilePath) : IO FilePath := do
  let target ← prepareEvent ctx base "reclassify"
  mutate target "claims.tsv" claim 5 "definition"
  mutate target "claims.tsv" claim 6 "definition"
  mutate target "claim-vocabulary-review.tsv" claim 2 shellReview
  add target "claim-normalization-reviews.tsv" #["NR-RUNTIME-0001", shellEvent, "1", claim,
    "exact_statement_readiness", "reclassify", "closed", "wrong-source-kind", shellReview]
  add target "claim-corrections.tsv" #["CC-RUNTIME-0001", shellEvent, "1", "NR-RUNTIME-0001", claim,
    "reclassify", "notation", "notation", "definition", "definition"]
  refresh ctx target
  pure target

/-- Produce a reviewed unchanged claim without inventing a correction row. -/
def makeUnchanged (ctx : Context) (base : FilePath) : IO FilePath := do
  let target ← prepareEvent ctx base "unchanged"
  add target "claim-normalization-reviews.tsv" #["NR-RUNTIME-UNCHANGED", shellEvent, "1", claim,
    "exact_statement_readiness", "unchanged", "closed", "exact-statement-ready", shellReview]
  pure target

/-- Produce a reviewed nonclaim exclusion while preserving its stable claim record. -/
def makeOutOfScope (ctx : Context) (base : FilePath) : IO FilePath := do
  let target ← prepareEvent ctx base "out-of-scope"
  for (col, value) in #[(5, "out_of_scope"), (9, "not-a-formalizable-claim"), (10, shellReview)] do
    mutate target "claims.tsv" "CL-TASAKI2020-0002" col value
  remove target "claim-vocabulary-review.tsv" "CL-TASAKI2020-0002"
  add target "claim-normalization-reviews.tsv" #["NR-RUNTIME-0002", shellEvent, "1", "CL-TASAKI2020-0002",
    "exact_statement_readiness", "exclude_nonclaim", "closed", "not-a-formalizable-claim", shellReview]
  add target "claim-corrections.tsv" #["CC-RUNTIME-0002", shellEvent, "1", "NR-RUNTIME-0002", "CL-TASAKI2020-0002",
    "exclude_nonclaim", "notation", "notation", "out_of_scope", "notation"]
  refresh ctx target
  pure target

/-- Produce the original two-atom source split with exact source-body bytes and item provenance. -/
def makeSplit (ctx : Context) (base : FilePath) : IO FilePath := do
  let target ← prepareEvent ctx base "split"
  let body1 := "For Problem 11.4.1.a, assume the stated local decay estimate."
  let body2 := "The estimate applies whenever the lattice distance exceeds one."
  let oid1 ← blob ctx body1
  let oid2 ← blob ctx body2
  let rows ← table target "claims.tsv"
  let mut output := #[]
  for row in rows do
    if row[0]! == "CL-TASAKI2020-3256" then
      output := output.push (row |>.set! 11 "true" |>.set! 12 "CL-TASAKI2020-9001" |>.set! 13 "compound-claim" |>.set! 14 shellReview)
      for (id, order, atom, body, oid) in #[("CL-TASAKI2020-9001", "000528.0005", "1/2", body1, oid1),
          ("CL-TASAKI2020-9002", "000528.0006", "2/2", body2, oid2)] do
        output := output.push #[id, "TASAKI2020", order, "PG-TASAKI2020-0528",
          "PDF p. 528; print p. 519; NONE; paragraph 7; correction split atom " ++ atom,
          "hypothesis", "hypothesis", body, oid, "NONE", "NONE", "false", "NONE", "NONE", "NONE"]
    else output := output.push row
  writeTable target "claims.tsv" output
  writeTable target "item-claims.tsv" <| insertAfter (← table target "item-claims.tsv")
    (fun r => r[0]?.getD "" == "IT-TASAKI2020-3034" && r[2]?.getD "" == "CL-TASAKI2020-3256")
    #[#["IT-TASAKI2020-3034", "2", "CL-TASAKI2020-9001"], #["IT-TASAKI2020-3034", "3", "CL-TASAKI2020-9002"]]
  remove target "claim-vocabulary-review.tsv" "CL-TASAKI2020-3256"
  for id in #["CL-TASAKI2020-9001", "CL-TASAKI2020-9002"] do
    add target "claim-vocabulary-review.tsv" #[id, "mathlib_only", shellReview]
  add target "claim-normalization-reviews.tsv" #["NR-RUNTIME-0003", shellEvent, "1", "CL-TASAKI2020-3256",
    "exact_statement_readiness", "split", "closed", "compound-claim", shellReview]
  add target "claim-corrections.tsv" #["CC-RUNTIME-0003", shellEvent, "1", "NR-RUNTIME-0003", "CL-TASAKI2020-3256",
    "split", "hypothesis", "hypothesis", "hypothesis", "hypothesis"]
  for (edge, position, id) in #[("SE-RUNTIME-0001", "1", "CL-TASAKI2020-9001"), ("SE-RUNTIME-0002", "2", "CL-TASAKI2020-9002")] do
    add target "claim-successors.tsv" #[edge, shellEvent, "CC-RUNTIME-0003", "CL-TASAKI2020-3256", position, "new_successor", id]
  refresh ctx target
  pure target

/-- Replace the second new split atom with an existing duplicate and remove its fresh records. -/
def replaceSecond (ctx : Context) (target : FilePath) (successor : String) : IO Unit := do
  mutate target "claim-successors.tsv" "SE-RUNTIME-0002" 5 "existing_duplicate"
  mutate target "claim-successors.tsv" "SE-RUNTIME-0002" 6 successor
  remove target "claims.tsv" "CL-TASAKI2020-9002"
  remove target "item-claims.tsv" "CL-TASAKI2020-9002" 2
  remove target "claim-vocabulary-review.tsv" "CL-TASAKI2020-9002"
  refresh ctx target

/-- Add the independently frozen second source used by source-binding rejection cases. -/
def addSourceB (ctx : Context) (target : FilePath) : IO Unit := do
  add target "sources.tsv" #["SRB", "TR-TASAKI", "2", "paper", "SRB2026", "Runtime Source B", "Runtime Author", "2026", "v1", "none",
    "NONE", "NONE", "source-b", "runtime-source-b.pdf", String.ofList (List.replicate 40 'a'), String.ofList (List.replicate 40 'b'), "frozen"]
  add target "source-progress.tsv" #["SRB", "vocabulary_reviewed", "RUNTIME-SOURCE-B-REVIEW"]
  add target "pages.tsv" #["PG-SRB-0001", "SRB", "000001", "1", "1", "1", "content", "complete", "complete", String.ofList (List.replicate 40 'c')]
  add target "claims.tsv" #["CL-SRB-0001", "SRB", "000001.0001", "PG-SRB-0001", "PDF p. 1; paragraph 1", "assertion", "theorem",
    "Runtime source B assertion.", "PENDING", "NONE", "NONE", "false", "NONE", "NONE", "NONE"]
  add target "source-items.tsv" #["IT-SRB-0001", "SRB", "000001.0001", "PG-SRB-0001", "theorem", "Theorem B", "Runtime theorem B",
    "PDF p. 1; Theorem B", "Runtime Source B", "runtime-source-b", "RUNTIME-SOURCE-B-REVIEW"]
  add target "item-claims.tsv" #["IT-SRB-0001", "1", "CL-SRB-0001"]
  add target "claim-vocabulary-review.tsv" #["CL-SRB-0001", "mathlib_only", "RUNTIME-SOURCE-B-REVIEW"]
  add target "source-invariants.tsv" #["SRB", "1", "1", "1", "0", "0", String.ofList (List.replicate 40 '0'), "RUNTIME-SOURCE-B-REVIEW"]
  refresh ctx target

/-- Restore the reviewed historical source item in an event-one snapshot when absent. -/
def addEventOneItem (target : FilePath) : IO Unit := do
  let items ← table target "source-items.tsv"
  if items.any (fun r => r[0]?.getD "" == "IT-TASAKI2020-3037") then return
  writeTable target "source-item-additions.tsv" #[#["item_addition_id", "event_id", "correction_id", "addition_position", "item_id", "review_ref"],
    #["IA-TASAKI2020-0001", "CORPUS-NORMALIZATION-TASAKI2020-2026", "CC-TASAKI2020-0012", "1", "IT-TASAKI2020-3037", "CORPUS-NORMALIZATION-INDEPENDENT-REVIEW"]]
  writeTable target "source-items.tsv" <| insertAfter items (fun r => r[0]?.getD "" == "IT-TASAKI2020-1537")
    #[#["IT-TASAKI2020-3037", "TASAKI2020", "000301.0003.0001", "PG-TASAKI2020-0301", "unlabeled", "NONE", "NONE",
      "PDF p. 301; print p. 289; §8.4; paragraph 6", "Chapter 08", "chapter-08", "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"]]
  let relations := (← table target "item-claims.tsv").filter fun r =>
    !(r[0]?.getD "" == "IT-TASAKI2020-1539" && #["CL-TASAKI2020-3442", "CL-TASAKI2020-3443"].contains (r[2]?.getD ""))
  writeTable target "item-claims.tsv" <| insertAfter relations (fun r => r[0]?.getD "" == "IT-TASAKI2020-1537")
    #[#["IT-TASAKI2020-3037", "1", "CL-TASAKI2020-3442"], #["IT-TASAKI2020-3037", "2", "CL-TASAKI2020-3443"]]

/-- Check the real historical transition and generated source-item counts as one original oracle. -/
def itemPublicContract (ctx : Context) (base current : FilePath) : IO Unit := do
  discard <| checked (ctx.command "corrections" #["--fixture-dirs", base.toString, current.toString])
  generate ctx current
  let items ← table current "source-items.tsv"
  ensure (items.size == 3038 && (items.filter fun r => r[8]?.getD "" == "Chapter 08").size == 363 &&
    (← table current "item-claims.tsv").size == 3191) "historical source-item counts"
  for id in #["IT-TASAKI2020-3036", "IT-TASAKI2020-3037"] do discard <| record current "source-items.tsv" id
  ensure (((← IO.FS.readFile (current / "docs/generated/sources/tasaki-2020.md")).splitOn "Reviewed source items: 3037").length > 1)
    "historical source-item source rendering"
  ensure (((← IO.FS.readFile (current / "docs/generated/groups/tasaki-2020/chapter-08.md")).splitOn "IT-TASAKI2020-3037").length > 1)
    "historical source-item group rendering"
/-- Transform only data records while preserving their exact table header. -/
def edit (root : FilePath) (name : String) (change : Array String → Array String) : IO Unit := do
  let rows ← table root name
  writeTable root name (rows.extract 0 1 ++ (rows.extract 1 rows.size).map change)

/-- Verify historical adapters preserve empty schemas and populated current-schema bytes. -/
def shellAdapterCases (ctx : Context) (base historical : FilePath) : IO Unit := do
  expectAction ctx "adapter-historical-empty-headers" true do
    for name in artifactNames do
      ensure ((← table historical name) == #[(← table ctx.project name)[0]!]) "historical adapter header or rows"
  let populated ← shellClone ctx base "adapter-current-populated"
  for (name, row) in #[
      ("bindings.tsv", #[claim, "LatticeSystem.Claims.Front.statement0001", "NONE", "LatticeSystem.Claims.Front", "definition", "notation_relation", "PENDING", "PENDING", "definitional", "NONE", "NONE", "NONE", "NONE", "NONE", "RUNTIME-REVIEW"]),
      ("axioms.tsv", #["AX-PROJECT-9001", "LatticeSystem.Axioms.State.fixture", "LatticeSystem.Axioms.State", "state", "fixture", "fixture", "remove", "PENDING"]),
      ("claim-context.tsv", #["CL-TASAKI2020-0002", "1", claim, "term_reference", "inherited", "RUNTIME-REVIEW"]),
      ("statement-modules.tsv", #["LatticeSystem.Claims.Front", "LatticeSystem/Claims/Front.lean", "leaf"]),
      ("statement-imports.tsv", #["LatticeSystem.Claims.Front", "1", "Mathlib", "true", "false", "false"])] do
    add populated name row
  expectAction ctx "adapter-current-populated-preserved" true do
    let before ← snapshot (populated / "registry")
    adaptEmpty ctx populated
    ensure ((← snapshot (populated / "registry")) == before) "adapter rewrote populated current schema"
  for name in #["bindings.tsv", "axioms.tsv"] do
    let target ← shellClone ctx base ("adapter-old-populated-" ++ name.replace ".tsv" "")
    IO.FS.writeFile (target / "registry" / name) (← git ctx.project #["show", baseCommit ++ ":registry/" ++ name])
    add target name #["historical", "populated", "artifact", "row", "must", "remain", "unchanged"]
    expectAction ctx ("adapter-old-populated-" ++ name) false (adaptEmpty ctx target)
      ("cannot migrate populated historical R4 fixture: " ++ name)

/-- Add a historical second item with either a moved or deliberately duplicated successor. -/
def addHistoricalItem (target : FilePath) (manifestId locator : String) (moveSecond : Bool) : IO Unit := do
  add target "source-item-additions.tsv" #[manifestId, "CORPUS-NORMALIZATION-TASAKI2020-2026", "CC-TASAKI2020-0012",
    "2", "IT-TASAKI2020-3038", "CORPUS-NORMALIZATION-INDEPENDENT-REVIEW"]
  writeTable target "source-items.tsv" <| insertAfter (← table target "source-items.tsv")
    (fun r => r[0]?.getD "" == "IT-TASAKI2020-3037")
    #[#["IT-TASAKI2020-3038", "TASAKI2020", "000301.0003.0002", "PG-TASAKI2020-0301", "unlabeled", "NONE", "NONE",
      locator, "Chapter 08", "chapter-08", "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"]]
  if moveSecond then
    edit target "item-claims.tsv" fun r =>
      if r[0]! == "IT-TASAKI2020-3037" && r[2]! == "CL-TASAKI2020-3443" then
        r |>.set! 0 "IT-TASAKI2020-3038" |>.set! 1 "1" else r
  else add target "item-claims.tsv" #["IT-TASAKI2020-3038", "1", "CL-TASAKI2020-3442"]

/-- Reject item addition identity, event, ownership, order and historical-provenance drift. -/
def shellItemCases (ctx : Context) (before current : FilePath) : IO Unit := do
  let duplicate ← shellClone ctx current "item-addition-id-duplicate"
  addHistoricalItem duplicate "IA-TASAKI2020-0001" "PDF p. 301; print p. 289; §8.4; paragraph 6 duplicate ID" true
  transition ctx "item-addition-id-duplicate" before duplicate false "duplicate source item addition ID"
  let double ← shellClone ctx current "item-double-manifest"
  add double "source-item-additions.tsv" #["IA-TASAKI2020-0099", "CORPUS-NORMALIZATION-TASAKI2020-2026", "CC-TASAKI2020-0012",
    "2", "IT-TASAKI2020-3037", "CORPUS-NORMALIZATION-INDEPENDENT-REVIEW"]
  transition ctx "item-double-manifest" before double false "source item is manifested more than once"
  for (label, name, id, col, value, diagnostic) in #[
      ("item-addition-id-invalid", "source-item-additions.tsv", "IA-TASAKI2020-0001", 0, "IA-bad", "bad source item addition ID"),
      ("item-correction-mismatch", "source-item-additions.tsv", "IA-TASAKI2020-0001", 2, "CC-TASAKI2020-0011", "source item addition event or correction mismatch"),
      ("item-event-mismatch", "source-item-additions.tsv", "IA-TASAKI2020-0001", 1, "CORPUS-NORMALIZATION-TASAKI2020-2027", "source item addition event or correction mismatch"),
      ("item-nested-key-malformed", "source-items.tsv", "IT-TASAKI2020-3037", 2, "000301.3.0001", "bad nested source item order key"),
      ("item-nested-key-inverted", "source-items.tsv", "IT-TASAKI2020-3037", 2, "000301.0005.0001", "source items are not in global source order")] do
    let target ← shellClone ctx current label
    mutate target name id col value
    transition ctx label before target false diagnostic
  let missing ← shellClone ctx current "item-missing-ledger"
  writeTable missing "source-item-additions.tsv" ((← table missing "source-item-additions.tsv").extract 0 1)
  transition ctx "item-missing-ledger" before missing false "unmanifested source item addition"
  let reused ← shellClone ctx current "item-existing-reregistration"
  add reused "source-item-additions.tsv" #["IA-TASAKI2020-0099", "CORPUS-NORMALIZATION-TASAKI2020-2026", "CC-TASAKI2020-0012", "2", "IT-TASAKI2020-1539", "CORPUS-NORMALIZATION-INDEPENDENT-REVIEW"]
  transition ctx "item-existing-reregistration" before reused false "source item addition reuses a frozen item ID"
  for (label, id, diagnostic) in #[("new-item-old-claim", "CL-TASAKI2020-1522", "new source item contains a frozen predecessor claim"),
      ("new-item-existing-duplicate", "CL-TASAKI2020-0349", "new source item contains an existing-duplicate successor"),
      ("new-item-different-correction", "CL-TASAKI2020-3430", "new source item contains a successor from a different correction")] do
    let target ← shellClone ctx current label
    edit target "item-claims.tsv" fun r => if r[0]! == "IT-TASAKI2020-3037" && r[1]! == "1" then r.set! 2 id else r
    transition ctx label before target false diagnostic
  let successorDuplicate ← shellClone ctx current "source-item-successor-duplicate"
  addHistoricalItem successorDuplicate "IA-TASAKI2020-0098" "PDF p. 301; print p. 289; §8.4; paragraph 6 duplicate" false
  transition ctx "source-item-successor-duplicate" before successorDuplicate false "correction successor occurs in more than one source item"
  let fig ← shellClone ctx current "fig-item-keeps-successors"
  add fig "item-claims.tsv" #["IT-TASAKI2020-1539", "2", "CL-TASAKI2020-3442"]
  add fig "item-claims.tsv" #["IT-TASAKI2020-1539", "3", "CL-TASAKI2020-3443"]
  transition ctx "fig-item-keeps-successors" before fig false "correction successor occurs in more than one source item"
  let edited ← shellClone ctx current "historical-item-edited"
  let row ← record edited "source-items.tsv" "IT-TASAKI2020-1539"
  mutate edited "source-items.tsv" row[0]! 7 (row[7]! ++ "; drift")
  transition ctx "historical-item-edited" before edited false "historical source item drift"
  let deleted ← shellClone ctx current "historical-item-deleted"
  remove deleted "source-items.tsv" "IT-TASAKI2020-1539"
  transition ctx "historical-item-deleted" before deleted false "historical source item drift"
  let moved ← shellClone ctx current "historical-relation-moved"
  edit moved "item-claims.tsv" fun r => if r[0]! == "IT-TASAKI2020-1539" && r[2]! == "CL-TASAKI2020-1523" then
    r |>.set! 0 "IT-TASAKI2020-3037" |>.set! 1 "3" else r
  transition ctx "historical-relation-moved" before moved false "historical source item relation drift"
  let ordinary ← shellClone ctx current "ordinary-unauthorized-item-add"
  writeTable ordinary "source-item-additions.tsv" ((← table ordinary "source-item-additions.tsv").extract 0 1)
  transition ctx "ordinary-unauthorized-item-add" current ordinary false "unmanifested source item addition"

/-- Create the complete second historical event with a newly owned nested source item. -/
def historicalSecond (ctx : Context) (current : FilePath) : IO Unit := do
  let target ← shellClone ctx current "historical-event2-new-item"
  let event := "CORPUS-NORMALIZATION-TASAKI2020-2027"
  let review := event ++ "-REVIEW"
  add target "correction-events.tsv" #[event, "2", "TASAKI2020", String.ofList (List.replicate 40 'd'), review]
  add target "claim-normalization-reviews.tsv" #["NR-TASAKI2020-2027-0001", event, "1", "CL-TASAKI2020-3256",
    "exact_statement_readiness", "split", "closed", "compound-claim", review]
  add target "claim-corrections.tsv" #["CC-TASAKI2020-2027-0001", event, "1", "NR-TASAKI2020-2027-0001", "CL-TASAKI2020-3256",
    "split", "hypothesis", "hypothesis", "hypothesis", "hypothesis"]
  let body := "For Problem 11.4.1.a, assume the stated local decay estimate."
  let rows ← table target "claims.tsv"
  let changed := rows.map fun r => if r[0]! == "CL-TASAKI2020-3256" then
    r |>.set! 11 "true" |>.set! 12 "CL-TASAKI2020-9003" |>.set! 13 "compound-claim" |>.set! 14 review else r
  writeTable target "claims.tsv" <| insertAfter changed (fun r => r[0]! == "CL-TASAKI2020-3256")
    #[#["CL-TASAKI2020-9003", "TASAKI2020", "000528.0004.0001", "PG-TASAKI2020-0528",
      "PDF p. 528; print p. 519; paragraph 7; event 2 successor", "hypothesis", "hypothesis", body,
      ← blob ctx body, "NONE", "NONE", "false", "NONE", "NONE", "NONE"]]
  add target "claim-successors.tsv" #["SE-TASAKI2020-2027-0001", event, "CC-TASAKI2020-2027-0001", "CL-TASAKI2020-3256", "1", "new_successor", "CL-TASAKI2020-9003"]
  remove target "claim-vocabulary-review.tsv" "CL-TASAKI2020-3256"
  add target "claim-vocabulary-review.tsv" #["CL-TASAKI2020-9003", "mathlib_only", review]
  add target "source-item-additions.tsv" #["IA-TASAKI2020-0002", event, "CC-TASAKI2020-2027-0001", "1", "IT-TASAKI2020-3038", review]
  writeTable target "source-items.tsv" <| insertAfter (← table target "source-items.tsv")
    (fun r => r[0]! == "IT-TASAKI2020-3034")
    #[#["IT-TASAKI2020-3038", "TASAKI2020", "000528.0004.0001", "PG-TASAKI2020-0528", "unlabeled", "NONE", "NONE",
      "PDF p. 528; print p. 519; paragraph 7; event 2 successor", "Solutions", "solutions", "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"]]
  writeTable target "item-claims.tsv" <| insertAfter (← table target "item-claims.tsv")
    (fun r => r[0]! == "IT-TASAKI2020-3034") #[#["IT-TASAKI2020-3038", "1", "CL-TASAKI2020-9003"]]
  refresh ctx target
  transition ctx "historical-event2-new-item" current target
/-- Execute one rejection after applying its exact isolated fixture mutation. -/
def shellNegative (ctx : Context) (base initial : FilePath) (label : String)
    (change : FilePath → IO Unit) (diagnostic : String) : IO Unit := do
  let target ← shellClone ctx initial label
  change target
  transition ctx label base target false diagnostic

/-- Check source binding for events, reviews, predecessors, successors and the selected census. -/
def shellSourceCases (ctx : Context) (base reclassify unchanged split : FilePath) : IO Unit := do
  shellNegative ctx base reclassify "event-source-bogus"
    (fun r => mutate r "correction-events.tsv" shellEvent 2 "BOGUS") "correction event source mismatch"
  shellNegative ctx base unchanged "unchanged-unknown-claim"
    (fun r => mutate r "claim-normalization-reviews.tsv" "NR-RUNTIME-UNCHANGED" 3 "CL-TASAKI2020-9999")
    "normalization review targets an unknown claim"
  for (label, successor, diagnostic) in #[("existing-duplicate-tombstone", "CL-TASAKI2020-0287", "existing duplicate successor is not active"),
      ("existing-duplicate-out-of-scope", "CL-TASAKI2020-2947", "existing duplicate successor is not a formalization target")] do
    shellNegative ctx base split label (fun r => replaceSecond ctx r successor) diagnostic
  let multi ← shellClone ctx base "multi-source-base"
  addSourceB ctx multi
  shellNegative ctx multi split "existing-duplicate-different-source" (fun r => do
    addSourceB ctx r
    replaceSecond ctx r "CL-SRB-0001") "correction successor source mismatch"
  let second ← prepareEvent ctx multi "multi-source-selected-second" "SRB"
  add second "claim-normalization-reviews.tsv" #["NR-RUNTIME-SRB-UNCHANGED", shellEvent, "1", "CL-SRB-0001",
    "exact_statement_readiness", "unchanged", "closed", "exact-statement-ready", shellReview]
  transition ctx "multi-source-selected-invariant-second" multi second
  shellNegative ctx multi second "multi-source-selected-invariant-stale" (fun r => do
    let row ← record r "source-invariants.tsv" "SRB"
    mutate r "source-invariants.tsv" "SRB" 2 (toString (row[2]!.toNat! + 1))) "census invariant count is stale"
  let mismatch ← prepareEvent ctx multi "review-source-mismatch"
  add mismatch "claim-normalization-reviews.tsv" #["NR-RUNTIME-SRB-MISMATCH", shellEvent, "1", "CL-SRB-0001",
    "exact_statement_readiness", "unchanged", "closed", "exact-statement-ready", shellReview]
  transition ctx "review-source-mismatch" multi mismatch false "normalization review source mismatch"
  let predecessor ← prepareEvent ctx multi "correction-predecessor-source-mismatch"
  mutate predecessor "claims.tsv" "CL-SRB-0001" 5 "definition"
  mutate predecessor "claims.tsv" "CL-SRB-0001" 6 "definition"
  mutate predecessor "claim-vocabulary-review.tsv" "CL-SRB-0001" 2 shellReview
  add predecessor "claim-normalization-reviews.tsv" #["NR-RUNTIME-SRB-RECLASSIFY", shellEvent, "1", "CL-SRB-0001",
    "exact_statement_readiness", "reclassify", "closed", "wrong-source-kind", shellReview]
  add predecessor "claim-corrections.tsv" #["CC-RUNTIME-SRB-RECLASSIFY", shellEvent, "1", "NR-RUNTIME-SRB-RECLASSIFY", "CL-SRB-0001",
    "reclassify", "assertion", "theorem", "definition", "definition"]
  refresh ctx predecessor
  transition ctx "correction-predecessor-source-mismatch" multi predecessor false "correction predecessor source mismatch"
  shellNegative ctx multi split "new-successor-source-mismatch" (fun r => do
    addSourceB ctx r
    for (col, value) in #[(1, "SRB"), (3, "PG-SRB-0001"), (2, "000002.0001")] do mutate r "claims.tsv" "CL-TASAKI2020-9002" col value
    refresh ctx r) "new successor source mismatch"

/-- Reject ledger shape drift and missing or reused split provenance. -/
def shellLedgerCases (ctx : Context) (base reclassify split : FilePath) : IO Unit := do
  let position := (← record reclassify "correction-events.tsv" shellEvent)[1]!.toNat! + 1
  for (label, initial, name, id, col, value, diagnostic) in #[
      ("event-position-gap", reclassify, "correction-events.tsv", shellEvent, 1, toString position, "invalid correction event ledger"),
      ("review-position-gap", reclassify, "claim-normalization-reviews.tsv", "NR-RUNTIME-0001", 2, "2", "invalid claim normalization review ledger"),
      ("correction-position-gap", reclassify, "claim-corrections.tsv", "CC-RUNTIME-0001", 2, "2", "invalid claim correction ledger"),
      ("correction-review-owner", reclassify, "claim-corrections.tsv", "CC-RUNTIME-0001", 3, "NR-TASAKI2020-0001", "invalid claim correction ledger"),
      ("successor-correction-owner", split, "claim-successors.tsv", "SE-RUNTIME-0001", 2, "CC-TASAKI2020-0001", "successor provenance has no split or duplicate retirement correction")] do
    shellNegative ctx base initial label (fun r => mutate r name id col value) diagnostic
  shellNegative ctx base split "split-existing-only" (fun r => do
    mutate r "claims.tsv" "CL-TASAKI2020-3256" 12 claim
    for id in #["CL-TASAKI2020-9001", "CL-TASAKI2020-9002"] do
      remove r "claims.tsv" id
      remove r "item-claims.tsv" id 2
      remove r "claim-vocabulary-review.tsv" id
    for (edge, target) in #[("SE-RUNTIME-0001", claim), ("SE-RUNTIME-0002", "CL-TASAKI2020-0002")] do
      mutate r "claim-successors.tsv" edge 5 "existing_duplicate"
      mutate r "claim-successors.tsv" edge 6 target
    refresh ctx r) "split requires a new successor"
  for (label, initial, name, id, col, diagnostic) in #[
      ("missing-event-review", reclassify, "correction-events.tsv", shellEvent, 0, "correction event is not reviewed"),
      ("disposition-without-ledger", reclassify, "claim-corrections.tsv", shellEvent, 1, "invalid claim correction ledger"),
      ("split-provenance-missing", split, "claim-successors.tsv", shellEvent, 1, "split successor provenance is incomplete")] do
    shellNegative ctx base initial label (fun r => remove r name id col) diagnostic
  shellNegative ctx base reclassify "unmanifested-claim-drift" (fun r => do
    let row ← record r "claims.tsv" "CL-TASAKI2020-0003"
    mutate r "claims.tsv" row[0]! 7 (row[7]! ++ " Unreviewed drift.")
    refresh ctx r) "unmanifested claim drift"
  shellNegative ctx base split "split-duplicate-position"
    (fun r => mutate r "claim-successors.tsv" "SE-RUNTIME-0002" 4 "1") "duplicate or noncontiguous successor position"
  for (label, successor, diagnostic) in #[("split-missing-successor", "CL-TASAKI2020-9999", "unknown correction successor"),
      ("split-id-reuse", "CL-TASAKI2020-0002", "new successor reuses a frozen claim ID")] do
    shellNegative ctx base split label (fun r => do
      mutate r "claim-successors.tsv" "SE-RUNTIME-0002" 6 successor
      remove r "claims.tsv" "CL-TASAKI2020-9002"
      remove r "item-claims.tsv" "CL-TASAKI2020-9002" 2
      remove r "claim-vocabulary-review.tsv" "CL-TASAKI2020-9002"
      refresh ctx r) diagnostic

/-- Reject retained predecessor vocabulary, lost item provenance and unrelated corpus drift. -/
def shellCorpusCases (ctx : Context) (base reclassify outOfScope split : FilePath) : IO Unit := do
  for (label, name, row, diagnostic) in #[
      ("tombstone-review-remains", "claim-vocabulary-review.tsv", #["CL-TASAKI2020-3256", "mathlib_only", shellReview], "excluded predecessor retains vocabulary review"),
      ("tombstone-use-remains", "claim-vocabulary.tsv", #["CL-TASAKI2020-3256", "VO-TASAKI2020-0001"], "excluded predecessor retains vocabulary use"),
      ("successor-item-duplicate", "item-claims.tsv", #["IT-TASAKI2020-3034", "4", "CL-TASAKI2020-9001"], "active successor has duplicate item provenance")] do
    shellNegative ctx base split label (fun r => add r name row) diagnostic
  shellNegative ctx base split "successor-item-missing"
    (fun r => remove r "item-claims.tsv" "CL-TASAKI2020-9002" 2) "active successor lacks the predecessor item"
  shellNegative ctx base reclassify "unrelated-frozen-row"
    (fun r => mutate r "source-items.tsv" "IT-TASAKI2020-0003" 6 "Unreviewed title drift") "unrelated frozen registry drift"
  for (label, col, value) in #[("unrelated-frozen-oid", 8, String.ofList (List.replicate 40 'a')),
      ("unrelated-frozen-locator", 4, (← record reclassify "claims.tsv" "CL-TASAKI2020-0003")[4]! ++ "; drift"),
      ("unrelated-frozen-order", 2, "000015.0099")] do
    shellNegative ctx base reclassify label (fun r => do
      mutate r "claims.tsv" "CL-TASAKI2020-0003" col value
      refresh ctx r) "unmanifested claim drift"
  for (label, initial, col, value, diagnostic) in #[
      ("stale-formalization-target-count", outOfScope, 3, toString ((← table outOfScope "source-invariants.tsv")[1]![3]!.toNat! + 1), "formalization target count is stale"),
      ("stale-census-oid", reclassify, 6, String.ofList (List.replicate 40 '0'), "census OID is stale")] do
    shellNegative ctx base initial label (fun r => do
      let id := (← table r "source-invariants.tsv")[1]![0]!
      mutate r "source-invariants.tsv" id col value) diagnostic
  shellNegative ctx base reclassify "final-counts-are-derived" (fun r => do
    let row := (← table r "source-invariants.tsv")[1]!
    for col in #[2, 3] do mutate r "source-invariants.tsv" row[0]! col (toString (row[col]!.toNat! + 1))) "census invariant count is stale"
  for (label, col, value, diagnostic) in #[
      ("contentless-true", 7, "True.", "contentless correction surrogate"),
      ("successor-oid-pending", 8, "PENDING", "new correction successor lacks a frozen content OID"),
      ("successor-oid-stale", 8, String.ofList (List.replicate 40 'a'), "new correction successor content OID is stale")] do
    shellNegative ctx base split label (fun r => do
      mutate r "claims.tsv" "CL-TASAKI2020-9002" col value
      refresh ctx r) diagnostic

/-- Reject every injected R4/axiom table and duplicate fresh-claim creation owner. -/
def shellArtifactCases (ctx : Context) (base reclassify split : FilePath) : IO Unit := do
  shellNegative ctx base reclassify "axiom-artifact" (fun r => do
    add r "axioms.tsv" #["AX-PROJECT-9001", "LatticeSystem.Axioms.ContentlessPredicate.correctionAxiom", "LatticeSystem.Axioms.ContentlessPredicate",
      "contentless_predicate", "TASAKI2020", "correction-surrogate", "replace-with-source-content", "PENDING"]
    add r "claim-axioms.tsv" #[claim, "AX-PROJECT-9001"]) "correction event introduces an axiom artifact"
  shellNegative ctx base reclassify "r4-artifact" (fun r =>
    add r "bindings.tsv" #[claim, "LatticeSystem.Claims.Front.statement0001", "LatticeSystem.Claims.Front.claim0001", "LatticeSystem.Claims.Front",
      "definition", "proof_proposition", "PENDING", "PENDING", "proof_stub", "theorem", "PENDING", "NONE", "NONE", "NONE", "CORRECTION-FIXTURE-REVIEW"])
    "correction event introduces an R4 artifact"
  shellNegative ctx base split "split-two-creation-owners" (fun r => do
    for (col, value) in #[(11, "true"), (12, "CL-TASAKI2020-9001"), (13, "compound-claim"), (14, shellReview)] do mutate r "claims.tsv" claim col value
    remove r "claim-vocabulary-review.tsv" claim
    add r "claim-normalization-reviews.tsv" #["NR-RUNTIME-TWO-OWNERS", shellEvent, "2", claim, "exact_statement_readiness", "split", "closed", "compound-claim", shellReview]
    add r "claim-corrections.tsv" #["CC-RUNTIME-TWO-OWNERS", shellEvent, "2", "NR-RUNTIME-TWO-OWNERS", claim, "split", "notation", "notation", "notation", "notation"]
    add r "claim-successors.tsv" #["SE-RUNTIME-TWO-OWNERS", shellEvent, "CC-RUNTIME-TWO-OWNERS", claim, "1", "new_successor", "CL-TASAKI2020-9001"]
    refresh ctx r) "split successor provenance is incomplete"
  for (label, name, row) in #[
      ("r4-artifact-claim-context", "claim-context.tsv", #["CL-TASAKI2020-0002", "1", claim, "assumption", "same_item", "CORRECTION-FIXTURE-REVIEW"]),
      ("r4-artifact-statement-modules", "statement-modules.tsv", #["LatticeSystem.Claims.Front", "LatticeSystem/Claims/Front.lean", "leaf"]),
      ("r4-artifact-statement-imports", "statement-imports.tsv", #["LatticeSystem.Claims.Front", "1", "Mathlib", "true", "false", "false"])] do
    shellNegative ctx base reclassify label (fun r => add r name row) "correction event introduces an R4 artifact"

/-- Run all production-derived correction and historical source-item cases. -/
def shellCases (ctx : Context) (base : FilePath) : IO Unit := do
  let passed ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let reclassify ← makeReclassify ctx base
  let outOfScope ← makeOutOfScope ctx base
  let split ← makeSplit ctx base
  let unchanged ← makeUnchanged ctx base
  let historicalBase := ctx.temporary / "cases/item-event1-base"
  let historicalCurrent := ctx.temporary / "cases/item-event1-current"
  cloneCommit ctx baseCommit historicalBase
  cloneCommit ctx eventOneCommit historicalCurrent
  addEventOneItem historicalCurrent
  expectAction ctx "event1-source-item-contract" true (itemPublicContract ctx historicalBase historicalCurrent)
  shellAdapterCases ctx base historicalCurrent
  shellItemCases ctx historicalBase historicalCurrent
  historicalSecond ctx historicalCurrent
  for (label, target) in #[("minimal-reclassify", reclassify), ("minimal-out-of-scope", outOfScope),
      ("minimal-split", split), ("minimal-unchanged-review", unchanged)] do transition ctx label base target
  shellSourceCases ctx base reclassify unchanged split
  shellLedgerCases ctx base reclassify split
  shellCorpusCases ctx base reclassify outOfScope split
  shellArtifactCases ctx base reclassify split
  ensure ((← ctx.accepted.get) - passed == 9 && (← ctx.rejected.get) - rejected == 62)
    "original correction matrix differs from 71 cases (9 positive, 62 rejection)"
/-- The synthetic source isolates duplicate-retirement behavior from production source assertions. -/
def dupSource : String := "SRD"

/-- The existing duplicate record preserved as the historical predecessor. -/
def predecessor : String := "CL-SRD-0001"

/-- The unchanged existing canonical target of a reviewed duplicate retirement. -/
def canonical : String := "CL-SRD-0002"

/-- An independent source claim used by ownership and unrelated-drift controls. -/
def other : String := "CL-SRD-0003"

/-- The independently reviewed duplicate-retirement event. -/
def dupEvent : String := "RUNTIME-DUPLICATE-RETIREMENT"

/-- The closed readiness review token for duplicate-retirement fixtures. -/
def dupReview : String := dupEvent ++ "-REVIEW"

/-- The owning correction's stable identity. -/
def dupCorrection : String := "CC-RUNTIME-DUPLICATE-0001"

/-- The owning normalization review's stable identity. -/
def dupNormalization : String := "NR-RUNTIME-DUPLICATE-0001"

/-- The single existing-successor relation required by duplicate retirement. -/
def dupEdge : String := "SE-RUNTIME-DUPLICATE-0001"

/-- Clone just the registry into an owned duplicate-protocol fixture. -/
def dupClone (ctx : Context) (before : FilePath) (name : String) : IO FilePath := do
  let after := ctx.temporary / "duplicate-retirement" / name
  copyRegistry ctx before after
  pure after

/-- Construct a complete synthetic three-claim source alongside the frozen actual corpus. -/
def duplicateBase (ctx : Context) : IO FilePath := do
  let base ← dupClone ctx ctx.project "base"
  add base "sources.tsv" #[dupSource, "TR-TASAKI", "2", "paper", "SRD2026", "Runtime duplicate protocol", "Runtime Author", "2026", "v1", "none",
    "NONE", "NONE", "runtime-duplicate", "runtime-duplicate.pdf", String.ofList (List.replicate 40 'a'), String.ofList (List.replicate 40 'b'), "frozen"]
  add base "source-progress.tsv" #[dupSource, "vocabulary_reviewed", "RUNTIME-DUPLICATE-BASE-REVIEW"]
  add base "pages.tsv" #["PG-SRD-0001", dupSource, "000001", "1", "1", "1", "content", "complete", "complete", String.ofList (List.replicate 40 'c')]
  for (position, id) in #[(1, predecessor), (2, canonical), (3, other)] do
    let order := "000001." ++ pad position
    let content := s!"Synthetic duplicate protocol private content {position}."
    let locator := s!"PDF p. 1; Equation (R.{position})"
    add base "claims.tsv" #[id, dupSource, order, "PG-SRD-0001", locator, "assertion", "equation", content,
      ← blob ctx content, "NONE", "NONE", "false", "NONE", "NONE", "NONE"]
    let item := "IT-SRD-" ++ pad position
    add base "source-items.tsv" #[item, dupSource, order, "PG-SRD-0001", "equation", s!"Equation (R.{position})", "NONE", locator,
      "Ungrouped", "ungrouped", "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"]
    add base "item-claims.tsv" #[item, "1", id]
    add base "claim-vocabulary-review.tsv" #[id, "mathlib_only", dupReview]
  add base "source-invariants.tsv" #[dupSource, "1", "3", "3", "3", "0", String.ofList (List.replicate 40 '0'), "RUNTIME-DUPLICATE-BASE-REVIEW"]
  refresh ctx base
  pure base

/-- Retire one existing duplicate without changing any canonical row or original membership. -/
def retirement (ctx : Context) (before : FilePath) (name : String) (commit : String := "") : IO FilePath := do
  let after ← dupClone ctx before name
  let actualCommit ← if commit.isEmpty then do
      let head ← git ctx.project #["rev-parse", "HEAD"]
      pure head.trimAscii.toString
    else pure commit
  add after "correction-events.tsv" #[dupEvent, toString (← table after "correction-events.tsv").size, dupSource, actualCommit, dupReview]
  add after "claim-normalization-reviews.tsv" #[dupNormalization, dupEvent, "1", predecessor, "exact_statement_readiness",
    "retire_duplicate", "closed", "same-source-atomic-assertion", dupReview]
  let old ← record before "claims.tsv" predecessor
  add after "claim-corrections.tsv" #[dupCorrection, dupEvent, "1", dupNormalization, predecessor, "retire_duplicate", old[5]!, old[6]!, old[5]!, old[6]!]
  add after "claim-successors.tsv" #[dupEdge, dupEvent, dupCorrection, predecessor, "1", "existing_duplicate", canonical]
  for (col, value) in #[(11, "true"), (12, canonical), (13, "same-source-atomic-assertion"), (14, dupReview)] do mutate after "claims.tsv" predecessor col value
  remove after "claim-vocabulary-review.tsv" predecessor
  mutate after "source-invariants.tsv" dupSource 7 dupReview
  refresh ctx after
  pure after

/-- Exercise dedicated and, when requested, explicitly owned base-diff transition routes. -/
def duplicateTransition (ctx : Context) (label : String) (before after : FilePath)
    (positive : Bool := true) (diagnostic : String := "") (both : Bool := false) : IO Unit := do
  transition ctx (label ++ "-dedicated") before after positive diagnostic
  if both then baseDiff ctx (label ++ "-base") before after positive dupEvent diagnostic

/-- Validate the actual structural registry and source-item contracts for a synthetic fixture. -/
def duplicateStatic (ctx : Context) (label : String) (root : FilePath) : IO Unit := do
  discard <| expect ctx (label ++ "-registry") true (ctx.gate "registry" root) "check-registry: ok"
  discard <| expect ctx (label ++ "-items") true (ctx.gate "source-items" root) "check-source-items: ok"

/-- Check immutable predecessor/canonical bytes, item/vocabulary provenance, history and derived counts. -/
def preserved (before after : FilePath) : IO Unit := do
  ensure ((← record before "claims.tsv" predecessor).extract 0 11 ==
    (← record after "claims.tsv" predecessor).extract 0 11) "duplicate predecessor columns 1--11"
  ensure ((← record before "claims.tsv" canonical) == (← record after "claims.tsv" canonical)) "duplicate canonical whole row"
  for name in #["source-items.tsv", "item-claims.tsv", "vocabulary.tsv", "modules.tsv", "imports.tsv"] do
    ensure ((← IO.FS.readBinFile (before / "registry" / name)) ==
      (← IO.FS.readBinFile (after / "registry" / name))) ("duplicate preserved " ++ name)
  for name in #["claim-vocabulary-review.tsv", "claim-vocabulary.tsv"] do
    let old := (← table before name).filter fun r => r[0]?.getD "" == canonical
    let new := (← table after name).filter fun r => r[0]?.getD "" == canonical
    ensure (old == new) ("duplicate canonical " ++ name)
  for name in historyTables do
    ensure ((← IO.FS.readFile (after / "registry" / name)).startsWith
      (← IO.FS.readFile (before / "registry" / name))) ("duplicate history prefix " ++ name)
  let old ← record before "source-invariants.tsv" dupSource
  let new ← record after "source-invariants.tsv" dupSource
  let equationLoss := if (← record before "claims.tsv" predecessor)[6]! == "equation" then 1 else 0
  ensure (new[2]!.toNat! + 1 == old[2]!.toNat! && new[3]!.toNat! + 1 == old[3]!.toNat! &&
    new[4]!.toNat! + equationLoss == old[4]!.toNat!) "duplicate counts follow predecessor subkind"
  ensure (new[7]! == dupReview) "duplicate selected invariant review"

/-- Execute an isolated duplicate-protocol rejection after refreshing its actual derived census. -/
def duplicateNegative (ctx : Context) (before initial : FilePath) (label : String)
    (change : FilePath → IO Unit) (diagnostic : String) (both : Bool := false) : IO FilePath := do
  let after ← dupClone ctx initial label
  change after
  refresh ctx after
  duplicateTransition ctx label before after false diagnostic both
  pure after

/-- Attach an independent same-event owner to the canonical target, optionally with real amendment provenance. -/
def addCanonicalOwner (ctx : Context) (root : FilePath) (action : String := "reclassify")
    (content : Option String := none) : IO Unit := do
  let old ← record root "claims.tsv" canonical
  add root "claim-normalization-reviews.tsv" #["NR-RUNTIME-DUPLICATE-0002", dupEvent, "2", canonical,
    "exact_statement_readiness", action, "closed", "canonical-owner-control", dupReview]
  add root "claim-corrections.tsv" #["CC-RUNTIME-DUPLICATE-0002", dupEvent, "2", "NR-RUNTIME-DUPLICATE-0002", canonical,
    action, old[5]!, old[6]!, old[5]!, old[6]!]
  if let some body := content then
    add root "claim-content-amendments.tsv" #["CA-RUNTIME-DUPLICATE-0001", dupEvent, "CC-RUNTIME-DUPLICATE-0002", canonical,
      ← blob ctx old[7]!, ← blob ctx body, String.ofList (List.replicate 40 'c'), dupReview]
    mutate root "claims.tsv" canonical 7 body
    mutate root "claims.tsv" canonical 8 (← blob ctx body)

/-- Positive duplicate-retirement fixtures and the canonical project-vocabulary control. -/
structure DuplicateFixtures where
  base : FilePath
  valid : FilePath
  projectBase : FilePath
  projectValid : FilePath
  vocabulary : Array String

/-- Build positive, non-equation and canonical-vocabulary controls, retaining their exact independent oracles. -/
def duplicatePositiveCases (ctx : Context) : IO DuplicateFixtures := do
  let base ← duplicateBase ctx
  let valid ← retirement ctx base "valid"
  duplicateStatic ctx "duplicate-base" base
  duplicateStatic ctx "duplicate-current" valid
  duplicateTransition ctx "duplicate-valid" base valid true "" true
  preserved base valid
  let nonEquationBase ← dupClone ctx base "non-equation-base"
  mutate nonEquationBase "claims.tsv" predecessor 6 "theorem"
  refresh ctx nonEquationBase
  let nonEquation ← retirement ctx nonEquationBase "non-equation-current"
  duplicateStatic ctx "non-equation-current" nonEquation
  duplicateTransition ctx "non-equation-counts" nonEquationBase nonEquation true "" true
  preserved nonEquationBase nonEquation
  let vocabulary := ((← table base "vocabulary.tsv").extract 1 (← table base "vocabulary.tsv").size).map (·[0]!)
  ensure (vocabulary.size >= 2) "two existing vocabulary declarations required"
  let projectBase ← dupClone ctx base "project-canonical-base"
  mutate projectBase "claim-vocabulary-review.tsv" canonical 1 "project_vocabulary"
  add projectBase "claim-vocabulary.tsv" #[canonical, vocabulary[0]!]
  let projectValid ← retirement ctx projectBase "project-canonical-valid"
  duplicateStatic ctx "project-canonical-base" projectBase
  duplicateStatic ctx "project-canonical-current" projectValid
  duplicateTransition ctx "project-canonical-valid" projectBase projectValid true "" true
  preserved projectBase projectValid
  let modules ← table base "modules.tsv"
  for entry in modules.extract 1 modules.size do
    let destination := base / entry[1]!
    if let some parent := destination.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile destination (← IO.FS.readBinFile (ctx.project / entry[1]!))
  discard <| expect ctx "duplicate-existing-vocabulary-environment" true
    (ctx.command "vocabulary" #["--fixture", base.toString]) "check-vocabulary: ok"
  pure ⟨base, valid, projectBase, projectValid, vocabulary⟩
/-- Check predecessor vocabulary basis, source membership, identity and each preserved field independently. -/
def duplicatePredecessorCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  let base := f.base
  let valid := f.valid
  let project ← dupClone ctx f.projectBase "project-predecessor-base"
  mutate project "claim-vocabulary-review.tsv" predecessor 1 "project_vocabulary"
  add project "claim-vocabulary.tsv" #[predecessor, f.vocabulary[0]!]
  duplicateStatic ctx "project-predecessor-base" project
  let projectCurrent ← retirement ctx project "project-predecessor-current"
  remove projectCurrent "claim-vocabulary.tsv" predecessor
  duplicateStatic ctx "project-predecessor-current" projectCurrent
  duplicateTransition ctx "project-predecessor-rejected" project projectCurrent false
    "duplicate retirement requires exactly one base mathlib_only review" true
  for (label, mode, diagnostic) in #[("missing-base-review", "missing", "duplicate retirement requires exactly one base mathlib_only review"),
      ("duplicate-base-review", "duplicate", "duplicate retirement requires exactly one base mathlib_only review"),
      ("forged-base-use", "use", "duplicate retirement predecessor has vocabulary uses")] do
    let before ← dupClone ctx base (label ++ "-base")
    if mode == "missing" then remove before "claim-vocabulary-review.tsv" predecessor
    else if mode == "duplicate" then add before "claim-vocabulary-review.tsv" (← record before "claim-vocabulary-review.tsv" predecessor)
    else add before "claim-vocabulary.tsv" #[predecessor, f.vocabulary[0]!]
    let after ← retirement ctx before (label ++ "-current")
    duplicateTransition ctx label before after false diagnostic
  discard <| duplicateNegative ctx base valid "current-predecessor-use"
    (fun r => add r "claim-vocabulary.tsv" #[predecessor, f.vocabulary[0]!]) "duplicate retirement predecessor has vocabulary uses"
  for (label, col, value, diagnostic) in #[
      ("unknown-predecessor", 0, "", "correction predecessor source mismatch"),
      ("excluded-predecessor", 5, "out_of_scope", "duplicate retirement requires a frozen active formal predecessor"),
      ("tombstoned-predecessor", 11, "true", "duplicate retirement requires a frozen active formal predecessor"),
      ("wrong-source-predecessor", 1, "TASAKI2020", "correction predecessor source mismatch")] do
    let before ← dupClone ctx base (label ++ "-base")
    if col == 0 then remove before "claims.tsv" predecessor else mutate before "claims.tsv" predecessor col value
    refresh ctx before
    duplicateTransition ctx label before valid false diagnostic
  let fresh ← dupClone ctx valid "fresh-predecessor"
  mutate fresh "claim-corrections.tsv" dupCorrection 4 "CL-SRD-9999"
  mutate fresh "claim-normalization-reviews.tsv" dupNormalization 3 "CL-SRD-9999"
  mutate fresh "claim-successors.tsv" dupEdge 3 "CL-SRD-9999"
  let extra := (← record fresh "claims.tsv" predecessor) |>.set! 0 "CL-SRD-9999" |>.set! 2 "000001.0004"
  add fresh "claims.tsv" extra
  refresh ctx fresh
  duplicateTransition ctx "fresh-predecessor" base fresh false "correction predecessor source mismatch"
  for (col, value, diagnostic) in #[
      (0, "CL-SRD-9999", "normalization review targets an unknown claim"),
      (1, "TASAKI2020", "duplicate retirement requires a frozen active formal predecessor"),
      (2, "000001.0001.0001", "unmanifested claim drift"), (3, "PG-SRD-9999", "unmanifested claim drift"),
      (4, "PDF p. 1; altered locator", "unmanifested claim drift"), (5, "definition", "unmanifested claim drift"),
      (6, "definition", "unmanifested claim drift"), (7, "Altered synthetic content.", "unmanifested claim drift"),
      (8, "PENDING", "unmanifested claim drift"), (9, "forged-exclusion", "unmanifested claim drift"),
      (10, "FORGED-REVIEW", "unmanifested claim drift")] do
    discard <| duplicateNegative ctx base valid ("frozen-predecessor-column-" ++ toString (col + 1)) (fun r => do
      mutate r "claims.tsv" predecessor col value
      if col == 5 || col == 6 then mutate r "claim-corrections.tsv" dupCorrection (col + 3) value) diagnostic
  for (col, value, diagnostic) in #[(11, "false", "invalid duplicate retirement transition"),
      (12, other, "tombstone does not name its first successor"), (13, "forged-rationale", "invalid duplicate retirement transition"),
      (14, "FORGED-REVIEW", "invalid duplicate retirement transition")] do
    discard <| duplicateNegative ctx base valid ("retirement-field-" ++ toString (col + 1))
      (fun r => mutate r "claims.tsv" predecessor col value) diagnostic
  let pendingBase ← dupClone ctx base "pending-base"
  mutate pendingBase "claims.tsv" predecessor 8 "PENDING"
  refresh ctx pendingBase
  let pending ← retirement ctx pendingBase "pending-current"
  duplicateStatic ctx "pending-current" pending
  duplicateTransition ctx "pending-oid-preserved" pendingBase pending true "" true
  ensure ((← record pending "claims.tsv" predecessor)[8]! == "PENDING") "pending predecessor OID retained"

/-- Check the exact one-existing-successor edge and existing active same-source canonical target. -/
def duplicateEdgeCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  for (label, mode, value) in #[("zero-successors", "remove", ""), ("two-successors", "add", ""),
      ("wrong-position", "position", "2"), ("new-successor-relation", "relation", "new_successor"),
      ("wrong-successor-owner", "owner", "CC-UNKNOWN-0001"), ("wrong-edge-predecessor", "predecessor", other),
      ("self-successor", "target", predecessor)] do
    discard <| duplicateNegative ctx f.base f.valid label (fun r => do
      if mode == "remove" then remove r "claim-successors.tsv" dupEdge
      else if mode == "add" then add r "claim-successors.tsv" #["SE-RUNTIME-DUPLICATE-0002", dupEvent, dupCorrection, predecessor, "2", "existing_duplicate", other]
      else
        let column := if mode == "position" then 4 else if mode == "relation" then 5 else if mode == "owner" then 2 else if mode == "predecessor" then 3 else 6
        mutate r "claim-successors.tsv" dupEdge column value)
      "duplicate retirement requires one existing successor at position 1"
  for (label, mode, col, value) in #[("unknown-canonical", "edge", 6, "CL-SRD-9999"),
      ("fresh-canonical", "remove", 0, ""), ("cross-source-canonical", "claim", 1, "TASAKI2020"),
      ("excluded-canonical", "claim", 5, "out_of_scope"), ("tombstoned-canonical", "claim", 11, "true")] do
    discard <| duplicateNegative ctx f.base f.valid label (fun r =>
      if mode == "edge" then mutate r "claim-successors.tsv" dupEdge col value
      else if mode == "remove" then remove r "claims.tsv" canonical else mutate r "claims.tsv" canonical col value)
      "duplicate retirement canonical is not a frozen same-source active formal target"
  for (label, col, value) in #[("base-excluded", 5, "out_of_scope"), ("base-tombstoned", 11, "true"), ("base-cross-source", 1, "TASAKI2020")] do
    let before ← dupClone ctx f.base (label ++ "-canonical")
    mutate before "claims.tsv" canonical col value
    refresh ctx before
    duplicateTransition ctx label before f.valid false "duplicate retirement canonical is not a frozen same-source active formal target"
  let absent ← dupClone ctx f.base "absent-base-canonical"
  remove absent "claims.tsv" canonical
  refresh ctx absent
  duplicateTransition ctx "canonical-must-exist-in-base" absent f.valid false "duplicate retirement canonical is not a frozen same-source active formal target"

/-- Reject canonical whole-row and vocabulary drift, including independently owned same-event changes. -/
def duplicateCanonicalCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  let amendment ← dupClone ctx f.valid "same-event-canonical-amendment"
  addCanonicalOwner ctx amendment "amend_content" (some "Synthetic corrected canonical content.")
  refresh ctx amendment
  duplicateStatic ctx "same-event-amendment" amendment
  discard <| expect ctx "same-event-canonical-amendment-provenance" true
    (ctx.content #["--transition", f.base.toString, amendment.toString, dupEvent]) "check-content-amendments: ok"
  duplicateTransition ctx "same-event-canonical-amendment" f.base amendment false "existing duplicate successor drift" true
  discard <| duplicateNegative ctx f.base f.valid "canonical-review-drift"
    (fun r => mutate r "claim-vocabulary-review.tsv" canonical 2 "OTHER-REVIEW") "duplicate retirement canonical vocabulary review drift"
  discard <| duplicateNegative ctx f.projectBase f.projectValid "canonical-use-drift"
    (fun r => add r "claim-vocabulary.tsv" #[canonical, f.vocabulary[1]!]) "duplicate retirement canonical vocabulary use drift"
  discard <| duplicateNegative ctx f.projectBase f.projectValid "canonical-use-removed"
    (fun r => remove r "claim-vocabulary.tsv" canonical) "duplicate retirement canonical vocabulary use drift"
  let ownerBase ← dupClone ctx f.base "owner-review-base"
  mutate ownerBase "claim-vocabulary-review.tsv" canonical 2 "EARLIER-CANONICAL-REVIEW"
  let owner ← retirement ctx ownerBase "owner-review-current"
  addCanonicalOwner ctx owner
  mutate owner "claim-vocabulary-review.tsv" canonical 2 dupReview
  duplicateStatic ctx "owner-review-base" ownerBase
  duplicateStatic ctx "owner-review-current" owner
  duplicateTransition ctx "same-event-owner-review-drift" ownerBase owner false "duplicate retirement canonical vocabulary review drift" true
  let use ← dupClone ctx f.projectValid "owner-use-current"
  addCanonicalOwner ctx use
  add use "claim-vocabulary.tsv" #[canonical, f.vocabulary[1]!]
  duplicateStatic ctx "owner-use-current" use
  duplicateTransition ctx "same-event-owner-use-drift" f.projectBase use false "duplicate retirement canonical vocabulary use drift" true

/-- Reject creator privileges, fresh claims, changed original items and duplicate canonical membership. -/
def duplicateItemCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  for (label, name, row, diagnostic) in #[
      ("retained-predecessor-review", "claim-vocabulary-review.tsv", #[predecessor, "mathlib_only", dupReview], "excluded predecessor retains vocabulary review"),
      ("retirement-owned-amendment", "claim-content-amendments.tsv", #["CA-RUNTIME-DUPLICATE-0001", dupEvent, dupCorrection, predecessor,
        String.ofList (List.replicate 40 'd'), String.ofList (List.replicate 40 'e'), String.ofList (List.replicate 40 'c'), dupReview], "duplicate retirement cannot own source items or content amendments"),
      ("retirement-owned-item", "source-item-additions.tsv", #["IA-RUNTIME-DUPLICATE-0001", dupEvent, dupCorrection, "1", "IT-SRD-9999", dupReview], "duplicate retirement cannot own source items or content amendments")] do
    discard <| duplicateNegative ctx f.base f.valid label (fun r => add r name row) diagnostic
  let newClaim := (← record f.base "claims.tsv" other) |>.set! 0 "CL-SRD-0004" |>.set! 2 "000001.0004"
  discard <| duplicateNegative ctx f.base f.valid "unowned-fresh-claim"
    (fun r => add r "claims.tsv" newClaim) "split successor provenance is incomplete"
  for id in #["IT-SRD-0001", "IT-SRD-0002"] do
    let pred := id.endsWith "0001"
    discard <| duplicateNegative ctx f.base f.valid ("edited-item-" ++ id)
      (fun r => mutate r "source-items.tsv" id 6 "Altered item title")
      (if pred then "historical source item drift" else "unrelated frozen registry drift")
    discard <| duplicateNegative ctx f.base f.valid ("deleted-item-" ++ id)
      (fun r => remove r "source-items.tsv" id) (if pred then "historical source item drift" else "unrelated frozen registry drift")
    discard <| duplicateNegative ctx f.base f.valid ("deleted-relation-" ++ id)
      (fun r => remove r "item-claims.tsv" id) (if pred then "historical source item relation drift" else "unrelated item-claim drift")
  let extra ← dupClone ctx f.valid "canonical-in-predecessor-item"
  add extra "item-claims.tsv" #["IT-SRD-0001", "2", canonical]
  duplicateTransition ctx "canonical-in-predecessor-item" f.base extra false "unrelated item-claim drift"
  discard <| expect ctx "canonical-unique-item" false (ctx.gate "source-items" extra) "claim occurs in more than one item"
/-- Reject pre-existing proof infrastructure and later source lifecycles at either transition side. -/
def duplicateEligibilityCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  let binding := #[other, "LatticeSystem.Claims.Runtime.statement", "LatticeSystem.Claims.Runtime.proof", "LatticeSystem.Claims.Runtime",
    "definition", "proof_proposition", "PENDING", "PENDING", "proof_stub", "theorem", "PENDING", "NONE", "NONE", "NONE", "RUNTIME-BINDING-REVIEW"]
  for (label, name, row, diagnostic) in #[
      ("source-bindings", "bindings.tsv", binding, "duplicate retirement source already has bindings"),
      ("slice", "slices.tsv", #["SL-RUNTIME-0001", "1", predecessor], "duplicate retirement predecessor has skeleton or axiom relations"),
      ("dependency-owner", "dependencies.tsv", #[predecessor, "requires", claim, "NONE"], "duplicate retirement predecessor has skeleton or axiom relations"),
      ("dependency-target", "dependencies.tsv", #[other, "requires", predecessor, "NONE"], "duplicate retirement predecessor has skeleton or axiom relations"),
      ("axiom", "claim-axioms.tsv", #[predecessor, "AX-RUNTIME-0001"], "duplicate retirement predecessor has skeleton or axiom relations"),
      ("context-owner", "claim-context.tsv", #[predecessor, "1", claim, "term_reference", "inherited", dupReview], "duplicate retirement predecessor has skeleton or axiom relations"),
      ("context-setup", "claim-context.tsv", #[other, "1", predecessor, "assumption", "inherited", dupReview], "duplicate retirement predecessor has skeleton or axiom relations")] do
    let before ← dupClone ctx f.base ("existing-" ++ label ++ "-base")
    if label == "context-setup" then
      mutate before "claims.tsv" predecessor 5 "definition"
      mutate before "claims.tsv" predecessor 6 "definition"
      refresh ctx before
    add before name row
    let after ← retirement ctx before ("existing-" ++ label ++ "-current")
    duplicateTransition ctx ("existing-" ++ label) before after false diagnostic
  for lifecycle in #["skeleton_frozen", "proof_active", "complete"] do
    let before ← dupClone ctx f.base (lifecycle ++ "-base")
    mutate before "source-progress.tsv" dupSource 1 lifecycle
    let after ← retirement ctx before (lifecycle ++ "-current")
    duplicateTransition ctx lifecycle before after false "duplicate retirement requires a pre-R4 source"
  discard <| duplicateNegative ctx f.base f.valid "current-lifecycle"
    (fun r => mutate r "source-progress.tsv" dupSource 1 "skeleton_frozen") "duplicate retirement requires a pre-R4 source"

/-- Reject malformed closed ownership, incomplete classification pairs and duplicate ledger rows. -/
def duplicateLedgerCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  for (label, name, id, col, value, diagnostic) in #[
      ("open-review", "claim-normalization-reviews.tsv", dupNormalization, 6, "open", "invalid claim normalization review ledger"),
      ("mismatched-review", "claim-normalization-reviews.tsv", dupNormalization, 8, "OTHER-REVIEW", "invalid claim normalization review ledger"),
      ("wrong-review-owner", "claim-corrections.tsv", dupCorrection, 3, "NR-UNKNOWN-0001", "invalid claim correction ledger"),
      ("none-old-disposition", "claim-corrections.tsv", dupCorrection, 6, "NONE", "NONE old classification requires add_omitted_claim"),
      ("none-old-subkind", "claim-corrections.tsv", dupCorrection, 7, "NONE", "NONE old classification requires add_omitted_claim"),
      ("mismatched-old-pair", "claim-corrections.tsv", dupCorrection, 7, "lemma", "correction ledger does not match claim transition"),
      ("mismatched-new-pair", "claim-corrections.tsv", dupCorrection, 9, "lemma", "correction ledger does not match claim transition")] do
    discard <| duplicateNegative ctx f.base f.valid label (fun r => mutate r name id col value) diagnostic
  for (name, id, diagnostic) in #[
      ("claim-normalization-reviews.tsv", dupNormalization, "invalid claim normalization review ledger"),
      ("claim-corrections.tsv", dupCorrection, "invalid claim correction ledger")] do
    discard <| duplicateNegative ctx f.base f.valid ("duplicate-" ++ name)
      (fun r => do
        let row ← record r name id
        add r name row) diagnostic

/-- Reject historical ledger value/order changes, unrelated data drift and infrastructure injection. -/
def duplicateHistoryCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  for name in historyTables do
    ensure ((← table f.base name).size > 2) ("historical rows required for prefix controls: " ++ name)
    for mode in #["value", "order"] do
      let diagnostic := if name == "source-item-additions.tsv" && mode == "value" then
        "unmanifested source item addition" else "historical correction ledger drift"
      discard <| duplicateNegative ctx f.base f.valid ("history-" ++ name ++ "-" ++ mode) (fun r => do
        let rows ← table r name
        let changed := if mode == "value" then rows.set! 1 (rows[1]!.set! (rows[1]!.size - 1) (rows[1]!.back! ++ "-FORGED"))
          else (rows.set! 1 rows[2]!).set! 2 rows[1]!
        let changed := if name == "correction-events.tsv" && mode == "order" then
          (changed.set! 1 (changed[1]!.set! 1 "1")).set! 2 (changed[2]!.set! 1 "2") else changed
        writeTable r name changed) diagnostic
  for (label, name, id, col, value) in #[
      ("page-fingerprint", "pages.tsv", "PG-SRD-0001", 9, String.ofList (List.replicate 40 'd')),
      ("source-fingerprint", "sources.tsv", dupSource, 14, String.ofList (List.replicate 40 'd')),
      ("vocabulary", "vocabulary.tsv", f.vocabulary[0]!, 7, String.ofList (List.replicate 40 'd')),
      ("module", "modules.tsv", (← table f.base "modules.tsv")[1]![0]!, 1, "Altered.lean"),
      ("import", "imports.tsv", (← table f.base "imports.tsv")[1]![0]!, 2, "Mathlib.Altered"),
      ("phase", "phase.tsv", "vocabulary", 0, "skeleton"),
      ("unrelated-source", "sources.tsv", "TASAKI2020", 5, "Altered title")] do
    discard <| duplicateNegative ctx f.base f.valid ("unrelated-" ++ label)
      (fun r => mutate r name id col value) "unrelated frozen registry drift"
  for (label, name, row, diagnostic) in #[
      ("r4-injection", "statement-modules.tsv", #["LatticeSystem.Claims.Runtime", "LatticeSystem/Claims/Runtime.lean", "leaf"], "correction event introduces an R4 artifact"),
      ("axiom-injection", "axioms.tsv", #["AX-RUNTIME-0001", "LatticeSystem.Axioms.State.runtime", "LatticeSystem.Axioms.State", "state", "Runtime source", "runtime-reason", "runtime-reopen", String.ofList (List.replicate 40 'a')], "correction event introduces an axiom artifact")] do
    discard <| duplicateNegative ctx f.base f.valid label (fun r => add r name row) diagnostic

/-- Check every derived invariant independently through both real transition entrypoints. -/
def duplicateCensusCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  for (col, diagnostic) in #[(2, "census invariant count is stale"), (3, "formalization target count is stale"),
      (4, "census invariant count is stale"), (5, "census invariant count is stale"), (6, "census OID is stale"),
      (7, "duplicate retirement lacks its event invariant review")] do
    let after ← dupClone ctx f.valid ("stale-invariant-" ++ toString col)
    let old := (← record after "source-invariants.tsv" dupSource)[col]!
    let value := if col < 6 then toString (old.toNat! + 1) else if col == 6 then
      String.ofList (List.replicate 40 'd') else "RUNTIME-DUPLICATE-BASE-REVIEW"
    mutate after "source-invariants.tsv" dupSource col value
    duplicateTransition ctx ("stale-invariant-" ++ toString col) f.base after false diagnostic true

/-- Check both original public equation items, the canonical successor link and private-byte exclusion. -/
def duplicatePublicCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  let publicRoot ← dupClone ctx f.valid "public"
  for (label, mode) in #[("duplicate-public-write", "--write"), ("duplicate-public-no-drift", "--check")] do
    discard <| expect ctx label true (ctx.docs #[mode,"--root",publicRoot.toString])
  let value ← catalog publicRoot
  let oldItem ← catalogItem value "IT-SRD-0001"
  let canonicalItem ← catalogItem value "IT-SRD-0002"
  let oldClaims ← jsonArray (← property oldItem "claims")
  let canonicalClaims ← jsonArray (← property canonicalItem "claims")
  ensure ((← jsonString (← property oldClaims[0]! "claim_id")) == predecessor &&
    (← jsonString (← property oldClaims[0]! "successor_claim")) == canonical &&
    (← jsonString (← property canonicalClaims[0]! "claim_id")) == canonical &&
    (← jsonString (← property canonicalItem "source_label")) == "Equation (R.2)") "public original provenance and successor"
  let text ← publicText (publicRoot / "docs")
  let mut tokens := #[dupEvent, dupReview, dupCorrection, "CA-RUNTIME-DUPLICATE", ".self-local", ctx.temporary.toString]
  let rows ← table f.base "claims.tsv"
  for row in rows.extract 1 rows.size do
    if row[1]! == dupSource then tokens := tokens ++ #[row[7]!, row[8]!]
  for token in tokens do ensure ((text.splitOn token).length == 1) "duplicate public output contains private bytes"

/-- Create a separately owned canonical content repair before or after duplicate retirement. -/
def canonicalContentEvent (ctx : Context) (before : FilePath) (name event commit : String) : IO FilePath := do
  let after ← dupClone ctx before name
  let review := event ++ "-REVIEW"
  let old ← record before "claims.tsv" canonical
  let body := "Synthetic canonical revision for " ++ event ++ "."
  let nr := "NR-" ++ event ++ "-0001"
  let cc := "CC-" ++ event ++ "-0001"
  add after "correction-events.tsv" #[event, toString (← table after "correction-events.tsv").size, dupSource, commit, review]
  add after "claim-normalization-reviews.tsv" #[nr, event, "1", canonical, "exact_statement_readiness", "amend_content", "closed", "runtime-repair", review]
  add after "claim-corrections.tsv" #[cc, event, "1", nr, canonical, "amend_content", old[5]!, old[6]!, old[5]!, old[6]!]
  add after "claim-content-amendments.tsv" #["CA-" ++ event ++ "-0001", event, cc, canonical, ← blob ctx old[7]!,
    ← blob ctx body, String.ofList (List.replicate 40 'c'), review]
  mutate after "claims.tsv" canonical 7 body
  mutate after "claims.tsv" canonical 8 (← blob ctx body)
  mutate after "claim-vocabulary-review.tsv" canonical 2 review
  mutate after "source-invariants.tsv" dupSource 7 review
  refresh ctx after
  pure after

/-- Stage and commit only the owned fixture registry, returning its exact synthetic commit. -/
def fixtureCommit (ctx : Context) (repo : FilePath) (message : String) : IO String := do
  ctx.owned repo
  discard <| git repo #["add", "registry"]
  discard <| git repo #["commit", "--allow-empty", "-qm", message]
  pure (← git repo #["rev-parse", "HEAD"]).trimAscii.toString

/-- Exercise actual Git merge-base selection and guard composition over repair/retirement/ordinary/later repair history. -/
def duplicateSelectorCases (ctx : Context) (f : DuplicateFixtures) : IO Unit := do
  ensure ((← IO.getEnv "CHECK_BASE_DIFF").isNone) "selector must use real base checker"
  let repo := ctx.temporary / "duplicate-retirement/git-chain"
  newTarget ctx repo
  IO.FS.createDirAll repo
  ctx.owned repo
  discard <| git repo #["init", "-q"]
  discard <| git repo #["config", "user.name", "phasetr"]
  discard <| git repo #["config", "user.email", "phasetr@gmail.com"]
  installRegistry ctx f.base repo
  let initial ← fixtureCommit ctx repo "Synthetic registry base"
  let repair ← canonicalContentEvent ctx f.base "earlier-canonical-repair" "RUNTIME-EARLIER-REPAIR" initial
  installRegistry ctx repair repo
  discard <| expect ctx "selector-earlier-canonical-repair" true (ctx.command "base-diff-ci" #[repo.toString, initial]) "check-base-diff-ci: ok"
  let repairSha ← fixtureCommit ctx repo "Synthetic accepted canonical repair"
  let retired ← retirement ctx repair "after-earlier-repair" repairSha
  duplicateStatic ctx "after-earlier-repair" retired
  installRegistry ctx retired repo
  let output ← expect ctx "selector-retirement-real" true (ctx.command "base-diff-ci" #[repo.toString, repairSha]) "check-base-diff-ci: ok"
  ensure ((output.splitOn "check-base-diff: ok").length > 1) "real selector delegates actual base checker"
  mutate repo "correction-events.tsv" dupEvent 3 initial
  discard <| expect ctx "selector-wrong-base" false (ctx.command "base-diff-ci" #[repo.toString, repairSha])
    "new correction event base commit does not match the actual merge base"
  installRegistry ctx retired repo
  discard <| expect ctx "selector-two-new-events" false (ctx.command "base-diff-ci" #[repo.toString, initial])
    "multiple new correction events require an explicit CI policy change"
  let retirementSha ← fixtureCommit ctx repo "Synthetic accepted retirement"
  let ordinarySha ← fixtureCommit ctx repo "Synthetic ordinary successor"
  let output ← expect ctx "selector-historical-ordinary" true (ctx.command "base-diff-ci" #[repo.toString, retirementSha]) "check-base-diff: ok"
  ensure ((output.splitOn "check-base-diff-ci: ok").length == 1) "historical event takes ordinary branch"
  for name in historyTables do
    ensure ((← IO.FS.readBinFile (repo / "registry" / name)) == (← IO.FS.readBinFile (retired / "registry" / name)))
      ("ordinary ledger unchanged: " ++ name)
  mutate repo "claims.tsv" predecessor 11 "false"
  discard <| expect ctx "selector-historical-reopening" false (ctx.command "base-diff-ci" #[repo.toString, retirementSha])
    "identity/order/locator/content/exclusion/supersession"
  installRegistry ctx retired repo
  baseDiff ctx "ordinary-unowned-retirement" repair retired false "" "claim-vocabulary-review.tsv stable-ID deletion"
  let later ← canonicalContentEvent ctx retired "later-canonical-repair" "RUNTIME-LATER-REPAIR" ordinarySha
  duplicateStatic ctx "later-canonical-repair" later
  discard <| expect ctx "later-canonical-content-helper" true
    (ctx.content #["--transition", retired.toString, later.toString, "RUNTIME-LATER-REPAIR"]) "check-content-amendments: ok"
  transition ctx "later-canonical-dedicated" retired later true "check-claim-corrections: ok"
  baseDiff ctx "later-canonical-base" retired later true "RUNTIME-LATER-REPAIR" "check-base-diff: ok"
  installRegistry ctx later repo
  discard <| expect ctx "selector-later-canonical-repair" true (ctx.command "base-diff-ci" #[repo.toString, ordinarySha]) "check-base-diff-ci: ok"

/-- Execute the complete synthetic duplicate-retirement matrix and all uncounted preservation oracles. -/
def duplicateCases (ctx : Context) : IO Unit := do
  let passed ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  IO.FS.createDirAll (ctx.temporary / "duplicate-retirement")
  let fixtures ← duplicatePositiveCases ctx
  duplicatePredecessorCases ctx fixtures
  duplicateEdgeCases ctx fixtures
  duplicateCanonicalCases ctx fixtures
  duplicateItemCases ctx fixtures
  duplicateEligibilityCases ctx fixtures
  duplicateLedgerCases ctx fixtures
  duplicateHistoryCases ctx fixtures
  duplicateCensusCases ctx fixtures
  duplicatePublicCases ctx fixtures
  duplicateSelectorCases ctx fixtures
  ensure ((← ctx.accepted.get) - passed == 47 && (← ctx.rejected.get) - rejected == 120)
    "duplicate matrix differs from 167 cases (47 positive, 120 rejection)"

/-- Run all reviewed correction protocols with exact immutable baseline and tracked-fixture exclusion oracles. -/
def run (ctx : Context) : IO Unit := do
  let accepted ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let base := ctx.temporary / "base"
  copyRegistry ctx ctx.project base
  IO.FS.createDirAll (ctx.temporary / "cases")
  let baseline ← snapshot (base / "registry")
  ensure ((← record base "claims.tsv" "CL-TASAKI2020-3436")[7]! ==
    "In the reported ground-state phase diagram of Hamiltonian (8.3.4), the Haldane phase is surrounded by the large-D, AF2, and AF3 phases, and the spins in AF2 and AF3 point in the 2-direction and the 3-direction, respectively.") "registered af-axis-labels content"
  ensure ((← record base "claims.tsv" "CL-TASAKI2020-3447")[7]! ==
    "Define the decorated hypercubic lattice by Λ := E ∪ (I × {1, 2}).") "registered decorated-lattice-source-notation content"
  shellCases ctx base
  duplicateCases ctx
  ensure ((← snapshot (base / "registry")) == baseline) "immutable runtime base changed"
  ensure ((← git ctx.project #["ls-files", "fixtures/**"]).trimAscii.toString.isEmpty) "tracked fixtures are forbidden"
  ensure ((← ctx.accepted.get) - accepted == 56 && (← ctx.rejected.get) - rejected == 182)
    "corrections inventory differs from 238 cases (56 positive, 182 rejection)"
  IO.println "test-claim-corrections-runtime: ok (238 cases; 56 positive, 182 rejection cases)"

end Checker.Tests.Corrections
