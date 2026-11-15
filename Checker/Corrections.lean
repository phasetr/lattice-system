import Checker.Content
import Checker.BaseDiff

/-! Independently owned source-correction transitions and their immutable history. -/
namespace Checker.Corrections
open Lean System Checker.CheckAll Checker.CheckAll.Registry Checker.BaseDiff

/-- Read data rows while distinguishing required input from optional historical ledgers. -/
def rows (snapshot : Snapshot) (stem : String) : Array Row :=
  records (snapshot.files["registry/" ++ stem ++ ".tsv"]?.getD "")

/-- Read a ledger's exact bytes. -/
def bytes (snapshot : Snapshot) (stem : String) : String :=
  snapshot.files["registry/" ++ stem ++ ".tsv"]?.getD ""

/-- The known immutable prefix of each permanent source-correction ledger. -/
def ledgerNames : Array String := #["correction-events", "claim-normalization-reviews", "claim-corrections",
  "claim-successors", "source-item-additions", "claim-content-amendments"]

/-- Correction-ledger tokens have the historical ASCII grammar, which excludes slashes. -/
def correctionToken (value : String) : Bool :=
  !value.isEmpty && alnum value.toList.head! &&
    value.toList.all (fun c => alnum c || "._:#@+-".contains c)

/-- Addition IDs permit a multi-segment event token and a four-digit final suffix. -/
def additionId (value : String) : Bool :=
  let parts := value.splitOn "-"
  let middle := String.intercalate "-" (parts.drop 1 |>.dropLast)
  value.startsWith "IA-" && correctionToken middle &&
    parts.getLast!.length == 4 && digits parts.getLast!

/-- Exact current schema of an owned permanent ledger. -/
def header (current : Snapshot) (stem : String) : IO Unit := do
  let some (_, expected) := headers.find? (·.1 == stem) | throw <| IO.userError "unknown correction table"
  require ((tableFromText (bytes current stem)).records[0]?.getD "" == expected) s!"bad {stem}.tsv header"

/-- Frozen records survive byte-for-byte and appended rows belong to the current event. -/
def freezeLedger (before current : Snapshot) (stem event : String) (eventColumn : Nat) : IO Unit := do
  unless before.files.contains ("registry/" ++ stem ++ ".tsv") do return
  require ((bytes current stem).startsWith (bytes before stem)) "historical correction ledger drift"
  let old := index (rows before stem)
  let after := rows current stem
  for (id, prior) in old do
    let matching := after.filter (col · 1 == id)
    require (matching.size == 1 && matching[0]! == prior) "historical correction ledger drift"
  for row in after do
    unless old.contains (col row 1) do
      require ((if eventColumn == 0 then col row 1 else col row eventColumn) == event)
        "historical correction ledger drift"

/-- Compare artifact records; only empty headers can migrate without changing an artifact. -/
def sameArtifact (before current : Snapshot) (stem : String) : Bool :=
  rows before stem == rows current stem && ((rows before stem).isEmpty ||
    (tableFromText (bytes before stem)).records[0]? == (tableFromText (bytes current stem)).records[0]?)

/-- Require the source-local, frozen canonical witness contract for duplicate retirement. -/
def duplicateEligibility (before current : Snapshot) (event source : String) : IO Unit := do
  let actions := (rows current "claim-corrections").filter fun r => col r 2 == event && col r 6 == "retire_duplicate"
  if actions.isEmpty then return
  let old := index (rows before "claims"); let after := index (rows current "claims")
  for snap in #[before,current] do
    let cs := index (rows snap "claims")
    let progress := (rows snap "source-progress").filter (col · 1 == source)
    require (progress.size == 1 && oneOf (col progress[0]! 2)
      "registered|source_frozen|census_pass1|census_pass2|census_reconciled|vocabulary_reviewed")
      "duplicate retirement requires a pre-R4 source"
    require (!(rows snap "bindings").any fun r => col (cs[col r 1]?.getD #[]) 2 == source)
      "duplicate retirement source already has bindings"
  for action in actions do
    let id := col action 5; let prior := old[id]?.getD #[]; let row := after[id]?.getD #[]
    require (prior.size == 15 && row.size == 15 && col prior 2 == source && col row 2 == source &&
      oneOf (col prior 6) "assertion|definition|notation|hypothesis|domain|conjecture" &&
      prior.extract 9 15 == #["NONE","NONE","false","NONE","NONE","NONE"])
      "duplicate retirement requires a frozen active formal predecessor"
    let basis := (rows before "claim-vocabulary-review").filter (col · 1 == id)
    require (basis.size == 1 && col basis[0]! 2 == "mathlib_only")
      "duplicate retirement requires exactly one base mathlib_only review"
    for snap in #[before,current] do
      require (!(rows snap "claim-vocabulary").any (col · 1 == id))
        "duplicate retirement predecessor has vocabulary uses"
      for (stem,columns) in #[("slices",#[3]),("dependencies",#[1,3]),("claim-axioms",#[1]),("claim-context",#[1,3])] do
        require (!(rows snap stem).any fun r => columns.any (col r · == id))
          "duplicate retirement predecessor has skeleton or axiom relations"
    let edges := (rows current "claim-successors").filter fun r => col r 2 == event && col r 3 == col action 1
    require (edges.size == 1 && projection edges[0]! #[4,5,6] == #[id,"1","existing_duplicate"] &&
      col edges[0]! 7 != id) "duplicate retirement requires one existing successor at position 1"
    let canonical := col edges[0]! 7; let canonicalOld := old[canonical]?.getD #[]
    let canonicalCurrent := after[canonical]?.getD #[]
    require (!canonicalOld.isEmpty && !canonicalCurrent.isEmpty && col canonicalOld 2 == source &&
      col canonicalCurrent 2 == source && oneOf (col canonicalOld 6) "assertion|definition|notation|hypothesis|domain|conjecture" &&
      oneOf (col canonicalCurrent 6) "assertion|definition|notation|hypothesis|domain|conjecture" &&
      col canonicalOld 12 == "false" && col canonicalCurrent 12 == "false")
      "duplicate retirement canonical is not a frozen same-source active formal target"
    require (canonicalOld == canonicalCurrent) "existing duplicate successor drift"
    for (stem,label) in #[("claim-vocabulary-review","review"),("claim-vocabulary","use")] do
      require (((rows before stem).filter (col · 1 == canonical)).qsort (· < ·) ==
        ((rows current stem).filter (col · 1 == canonical)).qsort (· < ·))
        s!"duplicate retirement canonical vocabulary {label} drift"
    for stem in #["source-item-additions","claim-content-amendments"] do
      require (!(rows current stem).any fun r => col r 2 == event && col r 3 == col action 1)
        "duplicate retirement cannot own source items or content amendments"

/-- Check event/review/correction ownership before reading any action-specific exception. -/
def ledgers (before current : Snapshot) (requested : String) : IO (String × String × String) := do
  for stem in #["claims","source-items","item-claims","claim-vocabulary-review","claim-vocabulary",
    "source-invariants","bindings","axioms","claim-axioms","pages","sources","tracks"] do
    require (before.files.contains ("registry/" ++ stem ++ ".tsv") &&
      current.files.contains ("registry/" ++ stem ++ ".tsv")) s!"missing registry/{stem}.tsv"
  for stem in ledgerNames do
    require (current.files.contains ("registry/" ++ stem ++ ".tsv")) s!"missing registry/{stem}.tsv"
  for stem in #["correction-events","claim-normalization-reviews","claim-corrections","claim-successors","source-item-additions"] do
    header current stem
  let mut additionIds : Std.HashSet String := {}; let mut additionItems : Std.HashSet String := {}
  for row in rows current "source-item-additions" do
    require (row.size == 6) "bad source item addition row"
    require (additionId (col row 1)) "bad source item addition ID"
    require (!additionIds.contains (col row 1)) "duplicate source item addition ID"
    require (!additionItems.contains (col row 5)) "source item is manifested more than once"
    additionIds := additionIds.insert (col row 1); additionItems := additionItems.insert (col row 5)
  let additions := index (rows current "source-item-additions")
  require ((rows before "source-item-additions").all fun r => additions[col r 1]? == some r)
    "unmanifested source item addition"
  let events := rows current "correction-events"
  let mut seen : Std.HashSet String := {}
  for i in [:events.size] do
    let row := events[i]!
    require (row.size == 5 && correctionToken (col row 1) && col row 2 == toString (i+1) &&
      !seen.contains (col row 1) && correctionToken (col row 3) && hex (col row 4) 40 && correctionToken (col row 5))
      "invalid correction event ledger"
    seen := seen.insert (col row 1)
  let oldEvents := index (rows before "correction-events")
  let fresh := events.filter fun r => !oldEvents.contains (col r 1)
  let event ← if requested.isEmpty then do
    require (fresh.size == 1) "correction event is not reviewed"
    pure (col fresh[0]! 1)
  else pure requested
  let selected := events.filter (col · 1 == event)
  require (selected.size == 1) "correction event is not reviewed"
  let source := col selected[0]! 3; let review := col selected[0]! 5
  require (((rows before "sources").filter (col · 1 == source)).size == 1 &&
    ((rows current "source-invariants").filter (col · 1 == source)).size == 1) "correction event source mismatch"
  for stem in ledgerNames do freezeLedger before current stem event (if stem == "correction-events" then 0 else 2)
  let eventIndex := index events
  let reviews := rows current "claim-normalization-reviews"
  let mut reviewIds : Std.HashSet String := {}; let mut reviewPositions : Std.HashMap String Nat := {}
  let mut reviewed : Std.HashSet (String × String) := {}
  for row in reviews do
    let owner := col row 2; let position := reviewPositions[owner]?.getD 0 + 1
    require (row.size == 9 && !reviewIds.contains (col row 1) && eventIndex.contains owner &&
      col row 3 == toString position && !reviewed.contains (owner,col row 4) &&
      col row 5 == "exact_statement_readiness" && oneOf (col row 6)
        "unchanged|reclassify|exclude_nonclaim|split|amend_content|amend_and_reclassify|retire_duplicate|add_omitted_claim" &&
      col row 7 == "closed" && correctionToken (col row 8) && col row 9 == col (eventIndex[owner]?.getD #[]) 5)
      "invalid claim normalization review ledger"
    reviewIds := reviewIds.insert (col row 1); reviewPositions := reviewPositions.insert owner position
    reviewed := reviewed.insert (owner,col row 4)
  let reviewIndex := index reviews
  let mut correctionIds : Std.HashSet String := {}; let mut correctionPositions : Std.HashMap String Nat := {}
  let mut reviewUses : Std.HashSet String := {}; let mut claimUses : Std.HashSet (String × String) := {}
  for row in rows current "claim-corrections" do
    let owner := col row 2; let position := correctionPositions[owner]?.getD 0 + 1
    let readiness := reviewIndex[col row 4]?.getD #[]
    require (row.size == 10 && !correctionIds.contains (col row 1) && eventIndex.contains owner &&
      col row 3 == toString position && !readiness.isEmpty && col readiness 2 == owner &&
      col readiness 4 == col row 5 && col readiness 6 == col row 6 && !reviewUses.contains (col row 4) &&
      !claimUses.contains (owner,col row 5) && oneOf (col row 6)
        "reclassify|exclude_nonclaim|split|amend_content|amend_and_reclassify|retire_duplicate|add_omitted_claim")
      "invalid claim correction ledger"
    correctionIds := correctionIds.insert (col row 1); correctionPositions := correctionPositions.insert owner position
    reviewUses := reviewUses.insert (col row 4); claimUses := claimUses.insert (owner,col row 5)
  for row in reviews do
    require ((col row 6 == "unchanged") != reviewUses.contains (col row 1)) "invalid claim correction ledger"
  let old := index (rows before "claims"); let after := index (rows current "claims")
  for row in (rows current "claim-corrections").filter (col · 2 == event) do
    unless col row 6 == "add_omitted_claim" do
      require (col (old[col row 5]?.getD #[]) 2 == source) "correction predecessor source mismatch"
  for row in reviews.filter (col · 2 == event) do
    let id := col row 4
    if col row 6 == "add_omitted_claim" then
      require (!old.contains id && after.contains id) "omitted claim must introduce a fresh claim ID"
      require (col (after[id]?.getD #[]) 2 == source) "normalization review source mismatch"
    else
      require (old.contains id && after.contains id) "normalization review targets an unknown claim"
      require (col (old[id]?.getD #[]) 2 == source) "normalization review source mismatch"
  return (event,source,review)

/-- Each action changes only its explicitly owned classification/content or tombstone fields. -/
def claimActions (before current : Snapshot) (event : String) : IO Unit := do
  let old := index (rows before "claims"); let after := index (rows current "claims")
  let actions := index ((rows current "claim-corrections").filter (col · 2 == event) |>.map fun row =>
    #[col row 5] ++ row)
  let reviews := index ((rows current "claim-normalization-reviews").filter (col · 2 == event) |>.map fun row =>
    #[col row 4] ++ row)
  for (id,prior) in old do
    let some row := after[id]? | throw <| IO.userError "unmanifested claim drift"
    let action := (actions[id]?.getD #[]).extract 1 11
    if action.isEmpty then require (prior == row) "unmanifested claim drift"
    else
      let readiness := (reviews[id]?.getD #[]).extract 1 10
      let kind := col action 6
      require (col readiness 6 == kind) "correction lacks owning review"
      require (projection action #[7,8,9,10] == #[col prior 6,col prior 7,col row 6,col row 7])
        "correction ledger does not match claim transition"
      let allowed := if kind == "reclassify" then #[6,7] else if kind == "amend_content" then #[8,9]
        else if kind == "amend_and_reclassify" then #[6,7,8,9]
        else if kind == "exclude_nonclaim" then #[6,10,11] else #[12,13,14,15]
      for i in [:prior.size] do require (allowed.contains (i+1) || prior[i]! == row[i]?.getD "") "unmanifested claim drift"
      if kind == "reclassify" then
        require (projection row #[12,10,11] == #["false","NONE","NONE"]) "invalid reclassify transition"
      else if kind == "exclude_nonclaim" then
        require (col row 6 == "out_of_scope" && col row 7 == col prior 7 && col row 12 == "false" &&
          col row 10 == col readiness 8 && col row 11 == col readiness 9) "invalid nonclaim exclusion"
      else if kind != "amend_content" && kind != "amend_and_reclassify" then
        require (col row 6 == col prior 6 && col row 7 == col prior 7 && col row 12 == "true" &&
          col row 13 != "NONE" && col row 14 == col readiness 8 && col row 15 == col readiness 9)
          (if kind == "retire_duplicate" then "invalid duplicate retirement transition" else "invalid split transition")
  for (id,packed) in actions do
    unless old.contains id do
      let action := packed.extract 1 11; let row := after[id]?.getD #[]
      require (col action 6 == "add_omitted_claim") "correction targets an unknown frozen claim"
      require (!row.isEmpty && projection action #[7,8,9,10] == #["NONE","NONE",col row 6,col row 7])
        "invalid omitted claim transition"
  for (id,row) in after do
    unless old.contains id do
      let text := (col row 8).trimAscii.toString
      require (!(col row 8).isEmpty && !oneOf text "True|True.|False|False.") "contentless correction surrogate"
      require (hex (col row 9) 40) "new correction successor lacks a frozen content OID"
      require (projection row #[12,10,11] == #["false","NONE","NONE"]) "new correction successor is not active"

/-- Source membership and canonical identities are checked independently of unrelated-row filters. -/
def successorIdentities (before current : Snapshot) (event source : String) : IO Unit := do
  let old := index (rows before "claims"); let after := index (rows current "claims")
  let actions := index ((rows current "claim-corrections").filter (col · 2 == event))
  for edge in (rows current "claim-successors").filter (col · 2 == event) do
    let prior := old[col edge 7]?.getD #[]; let row := after[col edge 7]?.getD #[]
    if col edge 6 == "new_successor" && !row.isEmpty then
      require (col row 2 == source) "new successor source mismatch"
    else if col edge 6 == "existing_duplicate" then
      require (col prior 2 == source) "correction successor source mismatch"
      require (col edge 7 != col (actions[col edge 3]?.getD #[]) 5) "existing duplicate successor is the correction predecessor"
      require (col prior 12 == "false" && col row 12 == "false") "existing duplicate successor is not active"
      require (col prior 6 != "out_of_scope" && col row 6 != "out_of_scope") "existing duplicate successor is not a formalization target"
      require (prior == row) "existing duplicate successor drift"

/-- Successor positions and exclusive creation ownership retain every historical identity. -/
def successors (project : FilePath) (before current : Snapshot) (event : String) : IO Unit := do
  let old := index (rows before "claims"); let after := index (rows current "claims")
  let actions := index ((rows current "claim-corrections").filter (col · 2 == event))
  let edges := (rows current "claim-successors").filter (col · 2 == event)
  let mut positions : Std.HashMap String Nat := {}; let mut ids : Std.HashSet String := {}
  let mut members : Std.HashSet (String × String) := {}; let mut newOwners : Std.HashMap String Nat := {}
  let mut omissions : Std.HashMap String Nat := {}
  for (_,action) in actions do
    if col action 6 == "add_omitted_claim" then omissions := omissions.insert (col action 5) (omissions[col action 5]?.getD 0 + 1)
  for edge in edges do
    let owner := col edge 3; let action := actions[owner]?.getD #[]
    require (edge.size == 7 && !ids.contains (col edge 1) && !action.isEmpty &&
      col action 5 == col edge 4 && oneOf (col action 6) "split|retire_duplicate")
      "successor provenance has no split or duplicate retirement correction; split successor provenance is incomplete"
    let position := positions[owner]?.getD 0 + 1
    require (digits (col edge 5) true && col edge 5 == toString position)
      "duplicate or noncontiguous successor position; split successor provenance is incomplete"
    require (oneOf (col edge 6) "new_successor|existing_duplicate") "bad successor relation; split successor provenance is incomplete"
    require (after.contains (col edge 7)) "unknown correction successor; split successor provenance is incomplete"
    require (col edge 6 != "new_successor" || !old.contains (col edge 7)) "new successor reuses a frozen claim ID; split successor provenance is incomplete"
    require (col edge 6 != "existing_duplicate" || old.contains (col edge 7)) "existing duplicate is not frozen; split successor provenance is incomplete"
    require (!members.contains (owner,col edge 7)) "duplicate correction successor; split successor provenance is incomplete"
    if position == 1 then
      let predecessor := after[col edge 4]?.getD #[]
      require (col predecessor 12 == "true") "successor predecessor is not tombstoned; split successor provenance is incomplete"
      require (col predecessor 13 == col edge 7) "tombstone does not name its first successor; split successor provenance is incomplete"
    if col edge 6 == "new_successor" then
      newOwners := newOwners.insert (col edge 7) (newOwners[col edge 7]?.getD 0 + 1)
      let row := after[col edge 7]?.getD #[]
      let actual ← output project "git" #["hash-object","--stdin"] (some (col row 8))
      require (col row 9 == trim actual) "new correction successor content OID is stale"
    positions := positions.insert owner position; ids := ids.insert (col edge 1)
    members := members.insert (owner,col edge 7)
  for (owner,action) in actions do
    if col action 6 == "split" then
      let owned := edges.filter (col · 3 == owner)
      require (!owned.isEmpty) "split successor provenance is incomplete"
      require (owned.any (col · 6 == "new_successor")) "split requires a new successor; split successor provenance is incomplete"
  for (id,_) in after do
    unless old.contains id do
      let omission := omissions[id]?.getD 0; let successor := newOwners[id]?.getD 0
      require (!(omission > 0 && successor > 0)) "new claim has both addition and successor ownership; split successor provenance is incomplete"
      require (omission + successor == 1) "split successor provenance is incomplete"

/-- Global item order, historical membership and exclusive new-item creation ownership. -/
def itemOwnership (before current : Snapshot) (event source review : String) : IO Unit := do
  let tracks := index (rows current "tracks"); let sources := index (rows current "sources")
  let mut previous := ""
  for item in rows current "source-items" do
    require (orderKey (col item 3)) "bad nested source item order key"
    let sourceRow := sources[col item 2]?.getD #[]
    let track := tracks[col sourceRow 2]?.getD #[]
    let key := pad 9 (toString ((col track 2).toNat?.getD 0)) ++ "." ++
      pad 9 (toString ((col sourceRow 3).toNat?.getD 0)) ++ "." ++ col item 3
    require (previous.isEmpty || previous < key) "source items are not in global source order"
    previous := key
  let actions := (rows current "claim-corrections").filter (col · 2 == event)
  let actionIndex := index actions
  let predecessors : Std.HashSet String := actions.foldl (fun result row => result.insert (col row 5)) {}
  let relatedItems : Std.HashSet String := (rows before "item-claims").foldl (fun result row =>
    if predecessors.contains (col row 3) then result.insert (col row 1) else result) {}
  let oldItems := index (rows before "source-items"); let items := index (rows current "source-items")
  let mut relatedDrift := false; let mut unrelatedDrift := false
  for (id,prior) in oldItems do
    if items[id]? != some prior then
      if relatedItems.contains id then relatedDrift := true else unrelatedDrift := true
  require (!relatedDrift) "historical source item drift"
  require (!unrelatedDrift) "unrelated frozen registry drift"
  let relations := rows current "item-claims"
  relatedDrift := false; unrelatedDrift := false
  for row in rows before "item-claims" do
    unless relations.contains row do
      if predecessors.contains (col row 3) then relatedDrift := true else unrelatedDrift := true
  require (!relatedDrift) "historical source item relation drift"
  require (!unrelatedDrift) "unrelated item-claim drift"
  let edges := (rows current "claim-successors").filter (col · 2 == event)
  let oldClaims := index (rows before "claims")
  let omissionOwners : Std.HashMap String String := actions.foldl (fun result row =>
    if col row 6 == "add_omitted_claim" then result.insert (col row 5) (col row 1) else result) {}
  let splitOwners : Std.HashMap String String := edges.foldl (fun result row =>
    if col row 6 == "new_successor" then result.insert (col row 7) (col row 3) else result) {}
  let existing : Std.HashSet String := edges.foldl (fun result row =>
    if col row 6 == "existing_duplicate" then result.insert (col row 7) else result) {}
  let mut additionPositions : Std.HashMap String Nat := {}
  let mut added : Std.HashMap String String := {}
  for row in rows current "source-item-additions" do
    if col row 2 != event then
      require (oldItems.contains (col row 5)) "source item addition event or correction mismatch"
    else
      let owner := col row 3; let action := actionIndex[owner]?.getD #[]
      let hasNew := actions.any (fun a => col a 1 == owner && col a 6 == "add_omitted_claim") ||
        edges.any (fun e => col e 3 == owner && col e 6 == "new_successor")
      require (!action.isEmpty && hasNew && col row 6 == review)
        "source item addition event or correction mismatch"
      let position := additionPositions[owner]?.getD 0 + 1
      require (col row 4 == toString position) "source item addition event or correction mismatch"
      require (!oldItems.contains (col row 5)) "source item addition reuses a frozen item ID"
      require (items.contains (col row 5) && col (items[col row 5]?.getD #[]) 2 == source)
        "source item addition source mismatch"
      added := added.insert (col row 5) owner
      additionPositions := additionPositions.insert owner position
  for (id,_) in items do
    require (oldItems.contains id || added.contains id) "unmanifested source item addition"
  let mut mismatched := false; let mut matched := false; let mut duplicated := false
  for (id,owner) in added do
    let members := relations.filter (col · 1 == id)
    require (!members.isEmpty) "unmanifested source item addition"
    let action := actionIndex[owner]?.getD #[]
    if col action 6 == "add_omitted_claim" then
      require (omissionOwners[col members[0]! 3]? == some owner)
        "new source item contains a successor from a different correction"
    else require (col action 6 == "split") "source item addition event or correction mismatch"
    for member in members do
      let claim := col member 3
      if oldClaims.contains claim then
        throw <| IO.userError (if existing.contains claim then
          "new source item contains an existing-duplicate successor" else "new source item contains a frozen predecessor claim")
      require (omissionOwners.contains claim || splitOwners.contains claim)
        "new source item contains a frozen predecessor claim"
      if (relations.filter (col · 3 == claim)).size > 1 then duplicated := true
      let matchesOwner := if col action 6 == "add_omitted_claim" then omissionOwners.contains claim
        else splitOwners[claim]? == some owner
      if matchesOwner then matched := true else mismatched := true
  require (!mismatched) (if matched then "new source item contains a successor from a different correction"
    else "source item addition event or correction mismatch")
  require (!duplicated) "correction successor occurs in more than one source item"

/-- Unrelated reviews, uses and item relations stay frozen while affected targets receive fresh reviews. -/
def propagation (before current : Snapshot) (event : String) : IO Unit := do
  let actions := (rows current "claim-corrections").filter (col · 2 == event)
  let edges := (rows current "claim-successors").filter fun r => col r 2 == event && col r 6 == "new_successor"
  let affected : Std.HashSet String := actions.foldl (fun result r => result.insert (col r 5)) {}
  let affected := edges.foldl (fun result r => result.insert (col r 7)) affected
  let unrelatedReviews := fun snap => index ((rows snap "claim-vocabulary-review").filter fun r => !affected.contains (col r 1))
  require (unrelatedReviews before == unrelatedReviews current) "unrelated vocabulary review drift"
  require (sameRows ((rows before "claim-vocabulary").filter fun r => !affected.contains (col r 1))
    ((rows current "claim-vocabulary").filter fun r => !affected.contains (col r 1))) "unrelated vocabulary use drift"
  let newClaims : Std.HashSet String := edges.foldl (fun result r => result.insert (col r 7)) {}
  let newClaims := actions.foldl (fun result r =>
    if col r 6 == "add_omitted_claim" then result.insert (col r 5) else result) newClaims
  let priorRelations := rows before "item-claims"
  let relations := rows current "item-claims"
  require (priorRelations.all relations.contains && relations.all (fun r =>
    priorRelations.contains r || newClaims.contains (col r 3))) "unrelated item-claim drift"
  let reviewIndex := index (rows current "claim-normalization-reviews")
  let vocabularyReviews := rows current "claim-vocabulary-review"
  let vocabularyUses := rows current "claim-vocabulary"
  for action in actions do
    let claim := col action 5
    let reviews := vocabularyReviews.filter (col · 1 == claim)
    if oneOf (col action 6) "reclassify|amend_content|amend_and_reclassify|add_omitted_claim" then
      require (reviews.size == 1 && col reviews[0]! 3 == col (reviewIndex[col action 4]?.getD #[]) 9)
        "reclassified claim lacks correction vocabulary review; correction relation propagation failed"
    else
      require reviews.isEmpty "excluded predecessor retains vocabulary review; correction relation propagation failed"
      require (!(vocabularyUses.any (col · 1 == claim))) "excluded predecessor retains vocabulary use; correction relation propagation failed"
  let claims := index (rows current "claims")
  for edge in edges do
    let claim := col edge 7
    if claims.contains claim then
      let memberships := relations.filter (col · 3 == claim)
      require (!memberships.isEmpty) "active successor lacks the predecessor item; correction relation propagation failed"
      require (memberships.size == 1) "active successor has duplicate item provenance; correction relation propagation failed"
      require (((vocabularyReviews.filter (col · 1 == claim)).size) == 1)
        "active successor lacks vocabulary review; correction relation propagation failed"

/-- Recompute the affected source's canonical counts and row-plus-LF census digest. -/
def invariants (project : FilePath) (before current : Snapshot) (event source review : String) : IO Unit := do
  header current "source-invariants"
  let old := index ((rows before "source-invariants").filter (col · 1 != source))
  let after := index ((rows current "source-invariants").filter (col · 1 != source))
  require (old == after) "unrelated source invariant drift"
  let invariant := ((rows current "source-invariants").find? (col · 1 == source)).getD #[]
  require (col invariant 1 == source) "correction event source mismatch"
  if (rows current "claim-corrections").any (fun r => col r 2 == event && col r 6 == "retire_duplicate") then
    require (col invariant 8 == review) "duplicate retirement lacks its event invariant review"
  let pages := (rows current "pages").filter (col · 2 == source)
  let sourceClaims := (rows current "claims").filter (col · 2 == source)
  let active := sourceClaims.filter (col · 12 == "false")
  let used : Std.HashSet String := active.foldl (fun result r => result.insert (col r 4)) {}
  let emptyPages := pages.foldl (fun n r => if used.contains (col r 1) then n else n+1) 0
  require (col invariant 3 == toString active.size &&
    col invariant 5 == toString ((active.filter (col · 7 == "equation")).size) &&
    col invariant 6 == toString emptyPages) "census invariant count is stale"
  require (col invariant 4 == toString ((active.filter (col · 6 != "out_of_scope")).size))
    "formalization target count is stale"
  let text := String.join <| (pages ++ sourceClaims).toList.map fun r => String.intercalate "\t" r.toList ++ "\n"
  require (col invariant 7 == trim (← output project "git" #["hash-object","--stdin"] (some text))) "census OID is stale"

/-- Validate the complete source-correction contract against two concrete directory snapshots. -/
def validate (project base target : FilePath) (requested : String := "") (recordedBase : Option String := none) : IO Unit := do
  let before ← snapshot base; let current ← snapshot target
  let (event,source,review) ← ledgers before current requested
  if let some baseCommit := recordedBase then
    let selected := (rows current "correction-events").find? (col · 1 == event)
    require (col (selected.getD #[]) 4 == baseCommit) "correction event base commit mismatch"
  duplicateEligibility before current event source
  Checker.Content.validateTransitionAt project base target event
  for stem in #["axioms","claim-axioms"] do
    require (sameArtifact before current stem) "correction event introduces an axiom artifact"
  for stem in #["bindings","claim-context","statement-modules","statement-imports"] do
    require (sameArtifact before current stem) "correction event introduces an R4 artifact"
  for (path,text) in before.files do
    let stem := ((path.dropPrefix "registry/").dropSuffix ".tsv").toString
    unless (#["claims","source-items","item-claims","claim-vocabulary-review","claim-vocabulary","source-invariants",
      "correction-events","claim-normalization-reviews","claim-corrections","claim-successors","source-item-additions",
      "claim-content-amendments","bindings","claim-context","statement-modules","statement-imports","axioms","claim-axioms"].contains stem) do
      require (current.files[path]? == some text) "unrelated frozen registry drift"
  claimActions before current event
  successorIdentities before current event source
  successors project before current event
  itemOwnership before current event source review
  propagation before current event
  invariants project before current event source review
  if (rows current "claim-corrections").any (fun r => col r 2 == event && col r 6 == "add_omitted_claim") then
    dataEntry project "registry" [target.toString]
    dataEntry project "source-items" [target.toString]
  IO.println "check-claim-corrections: ok"

end Checker.Corrections
