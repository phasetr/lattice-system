import Checker.Text
import Checker.Support
import Checker.RegistryIO

/-! Reviewed content amendments and omitted-claim creation provenance. -/
namespace Checker.Content
open System Checker.CheckAll

/-- A literal, unquoted TSV record. -/
abbrev Row := Array String

/-- The permanent amendment schema, including its original column order. -/
def amendmentHeader : Row := #["amendment_id", "event_id", "correction_id", "claim_id",
  "old_content_oid", "new_content_oid", "page_source_oid", "review_ref"]

/-- The actions which own a permanent content-amendment row. -/
def contentActions : Array String := #["amend_content", "amend_and_reclassify"]

/-- The classifications permitted for active correction targets. -/
def targetDispositions : Array String := #["assertion", "definition", "notation", "hypothesis", "domain", "conjecture"]

/-- The complete historical subkind vocabulary for combined corrections. -/
def subkinds : Array String := #["theorem", "lemma", "proposition", "corollary", "equation", "definition",
  "notation", "problem", "remark", "subclaim", "unnumbered_obligation", "hypothesis", "domain", "conjecture"]

/-- Reject malformed records rather than supplying a default field. -/
private def cell (row : Row) (column : Nat) : IO String :=
  match row[column]? with
  | some value => pure value
  | none => throw <| IO.userError "list index out of range"

/-- Parse QUOTE_NONE records: quotes are literal and all three physical newline forms terminate rows. -/
def parseRows (text : String) : Array Row := Id.run do
  if text.isEmpty then return #[]
  let text := (text.replace "\r\n" "\n").replace "\r" "\n"
  let lines := split text "\n"
  let lines := if text.endsWith "\n" then lines.pop else lines
  return lines.map fun line => if line.isEmpty then #[] else split line "\t"

/-- Read UTF-8 without rewriting the bytes used for historical prefix checks. -/
private def readText (path : FilePath) : IO String := do
  let raw ← IO.FS.readBinFile path
  match String.fromUTF8? raw with
  | some text => pure text
  | none => throw <| IO.userError "invalid UTF-8 registry input"

/-- Only an absent historical amendment ledger is optional; every other table is required. -/
private def rows (root : FilePath) (name : String) (optional : Bool := false) : IO (Array Row) := do
  let path := root / "registry" / name
  if optional && !(← path.pathExists) then return #[]
  let text ← if name == "sources.tsv" || name == "source-items.tsv" || name == "source-progress.tsv" || name == "source-invariants.tsv" ||
      Checker.RegistryIO.futureNames.contains (name.dropEnd 4).toString then
      Checker.RegistryIO.read root (name.dropEnd 4).toString .historical
    else readText path
  let data := parseRows text
  if name == "claim-content-amendments.tsv" then
    require (data[0]? == some amendmentHeader) "bad claim-content-amendments.tsv header"
  return data.extract 1 data.size

/-- Reuse one immutable pass's parsed rows, loading only at the original first-read position. -/
private def cachedRows (root : FilePath) (name : String) (cached : Option (Array Row)) :
    IO (Array Row × Option (Array Row)) := do
  if let some data := cached then return (data,cached)
  let data ← rows root name
  return (data,some data)

/-- Lookup and insertion order are both retained; diagnostics iterate the source records. -/
private structure Keyed where
  data : Array Row
  index : Std.HashMap String Row

/-- Match dictionary construction, including duplicate rejection after all IDs have been read. -/
private def keyed (root : FilePath) (name : String) : IO Keyed := do
  let data ← rows root name
  let index ← data.foldlM (fun index row => do pure (index.insert (← cell row 0) row))
    ({} : Std.HashMap String Row)
  require (index.size == data.size) ("duplicate ID in " ++ name)
  return ⟨data,index⟩

/-- Required dictionary indexing preserves rejection of missing event or claim IDs. -/
private def key (table : Keyed) (identifier : String) : IO Row :=
  match table.index[identifier]? with
  | some row => pure row
  | none => throw <| IO.userError ("'" ++ identifier ++ "'")

/-- Count records in their original order, retaining short-circuit field checks in each predicate. -/
private def countRows (data : Array Row) (predicate : Row → IO Bool) : IO Nat :=
  data.foldlM (fun count row => do pure (if ← predicate row then count+1 else count)) 0

/-- Select rows without changing their physical order or multiplicity. -/
private def selectRows (data : Array Row) (predicate : Row → IO Bool) : IO (Array Row) :=
  data.foldlM (fun result row => do pure (if ← predicate row then result.push row else result)) #[]

/-- Stop at the first matching record, as the original existential checks did. -/
private def anyRow (data : Array Row) (predicate : Row → IO Bool) : IO Bool := data.anyM predicate

/-- Preserve Unicode edge whitespace without changing the normalized body. -/
private def strip (text : String) : String := Checker.Text.strip text

/-- Empty text and bare True/False, with an optional period, are not source-content surrogates. -/
private def contentless (text : String) : Bool :=
  let value := strip text
  value.isEmpty || #["True","False","True.","False."].contains value

/-- Object identifiers are strictly lowercase ASCII hexadecimal, with either supported Git width. -/
def validOid (value : String) : Bool :=
  (value.length == 40 || value.length == 64) && value.toList.all fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Reviewed tokens have a leading ASCII alphanumeric and the historical punctuation alphabet. -/
private def token (value : String) : Bool :=
  let alnum := fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
  match value.toList with
  | [] => false
  | first :: rest => alnum first && rest.all (fun c => alnum c || "._:#@+-".contains c)

/-- An amendment ID contains a nonempty reviewed token and at least four final decimal digits. -/
private def amendmentId (value : String) : Bool :=
  let parts := value.splitOn "-"
  let middle := String.intercalate "-" ((parts.drop 1).dropLast)
  let ending := parts.getLast!
  value.startsWith "CA-" && token middle && ending.length ≥ 4 &&
    ending.toList.all (fun c => '0' ≤ c && c ≤ '9')

/-- Recognize a Unicode decimal digit without changing the original CLI number grammar. -/
private def decimal (c : Char) : Option Nat := Checker.Text.decimal c

/-- Parse event positions through the shared text input contract. -/
private def integer (value : String) : IO Int := Checker.Text.integer value

/-- Hash the exact UTF-8 body in the caller's original project, without adding a line terminator. -/
private def blob (project : FilePath) (content : String) : IO String :=
  return trim (← output project "git" #["hash-object","--stdin"] (some content))

/-- Omissions are statically owned, while their creation-time classification is checked at their own event. -/
private def additionsStatic (root : FilePath) : IO (Array Row) := do
  let events ← keyed root "correction-events.tsv"
  let reviews ← keyed root "claim-normalization-reviews.tsv"
  let claims ← keyed root "claims.tsv"
  let pages ← keyed root "pages.tsv"
  let items ← keyed root "source-items.tsv"
  let corrections ← keyed root "claim-corrections.tsv"
  let (additions,_,_,_) ← corrections.data.foldlM (fun (additions,created,successors,itemClaims) correction => do
    if (← cell correction 5) != "add_omitted_claim" then
      require (!(correction.extract 6 8).contains "NONE") "NONE old classification requires add_omitted_claim"
      return (additions,created,successors,itemClaims)
    let eventId ← cell correction 1
    let reviewId ← cell correction 3
    let claimId ← cell correction 4
    let mismatch := "omitted claim review or source ownership mismatch"
    let some event := events.index[eventId]? | throw <| IO.userError mismatch
    let some review := reviews.index[reviewId]? | throw <| IO.userError mismatch
    let some claim := claims.index[claimId]? | throw <| IO.userError mismatch
    require ((← cell review 1) == (← cell event 0)) mismatch
    require ((← cell review 3) == (← cell claim 0)) mismatch
    require (review.extract 4 7 == #["exact_statement_readiness","add_omitted_claim","closed"]) mismatch
    require ((← cell review 8) == (← cell event 4)) mismatch
    require ((← cell claim 1) == (← cell event 2)) mismatch
    let reviewCount ← countRows reviews.data fun row => do
      if (← cell row 1) != (← cell event 0) then return false
      return (← cell row 3) == (← cell claim 0)
    require (reviewCount == 1) "omitted claim lacks exactly one owning review and correction"
    let correctionCount ← countRows corrections.data fun row => do
      if (← cell row 1) != (← cell event 0) then return false
      return (← cell row 4) == (← cell claim 0)
    require (correctionCount == 1) "omitted claim lacks exactly one owning review and correction"
    let invalid := "invalid omitted claim classification"
    require (correction.extract 6 8 == #["NONE","NONE"]) invalid
    require (targetDispositions.contains (← cell correction 8)) invalid
    require (subkinds.contains (← cell correction 9)) invalid
    let id ← cell claim 0
    require (!created.contains id) "omitted claim has more than one creation owner"
    let created := created.insert id
    let some page := pages.index[← cell claim 3]? | throw <| IO.userError "omitted claim source page mismatch"
    require ((← cell page 1) == (← cell event 2)) "omitted claim source page mismatch"
    let (successorRows,successors) ← cachedRows root "claim-successors.tsv" successors
    let hasSuccessor ← anyRow successorRows fun row => do
      if (← cell row 1) != (← cell event 0) then return false
      if (← cell row 2) == (← cell correction 0) then return true
      if (← cell row 3) == id then return true
      return (← cell row 6) == id
    require (!hasSuccessor) "omitted claim cannot have successor provenance"
    let (itemRows,itemClaims) ← cachedRows root "item-claims.tsv" itemClaims
    let relations ← selectRows itemRows fun row => return (← cell row 2) == id
    require (relations.size == 1) "omitted claim lacks exactly one source item"
    let some item := items.index[← cell relations[0]! 0]? | throw <| IO.userError "omitted claim source item mismatch"
    require ((← cell item 1) == (← cell event 2)) "omitted claim source item mismatch"
    require ((← cell item 3) == (← cell claim 3)) "omitted claim source item mismatch"
    pure (additions.push correction,created,successors,itemClaims))
    ((#[],{},none,none) : Array Row × Std.HashSet String × Option (Array Row) × Option (Array Row))
  return additions

/-- Reject an already bound source, using that snapshot's own claim-to-source lookup. -/
private def preR4 (root : FilePath) (claims : Keyed) (source label : String) : IO Unit := do
  let progress ← keyed root "source-progress.tsv"
  let some progress := progress.index[source]? | throw <| IO.userError (label ++ " requires a pre-R4 source")
  require (#["registered","source_frozen","census_pass1","census_pass2","census_reconciled","vocabulary_reviewed"].contains
    (← cell progress 1)) (label ++ " requires a pre-R4 source")
  for binding in ← rows root "bindings.tsv" do
    if let some claim := claims.index[← cell binding 0]? then
      require ((← cell claim 1) != source) (label ++ " source already has bindings")

/-- Reject creation-time skeleton, dependency or axiom ownership in either immutable snapshot. -/
private def noRelations (base current : FilePath) (claim message : String) : IO Unit := do
  for root in #[base,current] do
    for (name,columns) in #[("slices.tsv",#[2]),("dependencies.tsv",#[0,2]),("claim-axioms.tsv",#[0])] do
      for record in ← rows root name do
        for column in columns do require ((← cell record column) != claim) message

/-- Check omitted claims against their creation event, never retroactively against later corrections. -/
private def additionsTransition (project base current : FilePath) (event : Row)
    (validatedAdditions : Array Row) : IO Unit := do
  let additions ← selectRows validatedAdditions fun row => return (← cell row 1) == (← cell event 0)
  if additions.isEmpty then return
  let oldClaims ← keyed base "claims.tsv"
  let claims ← keyed current "claims.tsv"
  let oldPages ← keyed base "pages.tsv"
  let pages ← keyed current "pages.tsv"
  let sourceId ← cell event 2
  let oldSources ← keyed base "sources.tsv"
  let sources ← keyed current "sources.tsv"
  let message := "omitted claim source fingerprints changed or are not frozen"
  let some source := sources.index[sourceId]? | throw <| IO.userError message
  require (oldSources.index[sourceId]? == some source) message
  require (validOid (← cell source 14)) message
  require (validOid (← cell source 15)) message
  require ((← cell source 14).length == (← cell source 15).length) message
  preR4 base oldClaims sourceId "omitted claim"
  preR4 current claims sourceId "omitted claim"
  let vocabulary ← keyed current "vocabulary.tsv"
  let invariants ← keyed current "source-invariants.tsv"
  let some invariant := invariants.index[sourceId]? | throw <| IO.userError "omitted claim lacks its event invariant review"
  require ((← cell invariant 7) == (← cell event 4)) "omitted claim lacks its event invariant review"
  let pageCount ← countRows pages.data fun row => return (← cell row 1) == sourceId
  require ((← integer (← cell invariant 1)) == Int.ofNat pageCount) "omitted claim physical page count is stale"
  for correction in additions do
    let claimId ← cell correction 4
    require (!oldClaims.index.contains claimId) "omitted claim reuses a frozen claim ID"
    let claim ← key claims claimId
    require (claim.extract 5 7 == correction.extract 8 10) "omitted claim classification does not match its correction"
    require ((← cell claim 5) != "out_of_scope") "omitted claim is not an active formalization target"
    require (claim.extract 9 claim.size == #["NONE","NONE","false","NONE","NONE","NONE"])
      "omitted claim is not an active formalization target"
    let content ← cell claim 7
    require (!contentless content) "contentless omitted claim surrogate"
    let oid ← cell claim 8
    require (validOid oid) "omitted claim content OID is not frozen or is stale"
    require ((← blob project content) == oid) "omitted claim content OID is not frozen or is stale"
    let pageId ← cell claim 3
    let message := "omitted claim must use an unchanged frozen source page"
    let some oldPage := oldPages.index[pageId]? | throw <| IO.userError message
    require (pages.index[pageId]? == some oldPage) message
    require ((← cell oldPage 1) == sourceId) message
    require (validOid (← cell oldPage 9)) message
    noRelations base current claimId "omitted claim has skeleton or axiom relations"
    let reviews ← selectRows (← rows current "claim-vocabulary-review.tsv") fun row => return (← cell row 0) == claimId
    let uses ← selectRows (← rows current "claim-vocabulary.tsv") fun row => return (← cell row 0) == claimId
    let message := "omitted claim lacks its reviewed vocabulary basis and use"
    require (reviews.size == 1) message
    require ((← cell reviews[0]! 2) == (← cell event 4)) message
    let basis ← cell reviews[0]! 1
    require (#["mathlib_only","project_vocabulary"].contains basis) message
    if basis == "mathlib_only" then require uses.isEmpty message
    if basis == "project_vocabulary" then require (!uses.isEmpty) message
    let used ← uses.foldlM (fun used row => do pure (used.insert (← cell row 1)))
      ({} : Std.HashSet String)
    require (used.size == uses.size) message
    for row in uses do require (vocabulary.index.contains (← cell row 1)) message

/-- Validate a single static snapshot and retain its omission results for the same transition invocation. -/
private def validateContent (root : FilePath) : IO (Array Row × Array Row) := do
  let amendments ← rows root "claim-content-amendments.tsv"
  let events ← keyed root "correction-events.tsv"
  let corrections ← keyed root "claim-corrections.tsv"
  let reviews ← keyed root "claim-normalization-reviews.tsv"
  let claims ← keyed root "claims.tsv"
  let pages ← keyed root "pages.tsv"
  let (_,owned,history,historyOrder) ← amendments.foldlM (fun (seen,owned,history,historyOrder) row => do
    require (row.size == amendmentHeader.size) "bad content amendment row"
    let identifier := row[0]!; let eventId := row[1]!; let correctionId := row[2]!; let claimId := row[3]!
    let oldOid := row[4]!; let newOid := row[5]!; let pageOid := row[6]!; let reviewRef := row[7]!
    require (amendmentId identifier) "bad content amendment ID"
    require (!seen.contains identifier && !owned.contains correctionId) "duplicate content amendment"
    let seen := seen.insert identifier; let owned := owned.insert correctionId
    let message := "content amendment event or correction ownership mismatch"
    let some correction := corrections.index[correctionId]? | throw <| IO.userError message
    let some event := events.index[eventId]? | throw <| IO.userError message
    let some claim := claims.index[claimId]? | throw <| IO.userError message
    require ((← cell correction 1) == eventId) message
    require ((← cell correction 4) == claimId) message
    let action ← cell correction 5
    require (contentActions.contains action) message
    let message := "content amendment review ownership mismatch"
    let some review := reviews.index[← cell correction 3]? | throw <| IO.userError message
    require ((← cell review 1) == eventId) message
    require ((← cell review 3) == claimId) message
    require ((← cell review 5) == action) message
    require ((← cell review 4) == "exact_statement_readiness") message
    require ((← cell review 6) == "closed") message
    require (reviewRef == (← cell event 4)) message
    require ((← cell review 8) == reviewRef) message
    require (token reviewRef) message
    require ((← cell claim 1) == (← cell event 2)) "content amendment source mismatch"
    if action == "amend_and_reclassify" then
      let message := "combined correction lacks exactly one owning review and correction"
      let reviewCount ← countRows reviews.data fun record => do
        if (← cell record 1) != eventId then return false
        return (← cell record 3) == claimId
      require (reviewCount == 1) message
      let correctionCount ← countRows corrections.data fun record => do
        if (← cell record 1) != eventId then return false
        return (← cell record 4) == claimId
      require (correctionCount == 1) message
      let message := "combined correction has invalid classification"
      require (correction.size == 10) message
      require (targetDispositions.contains (← cell correction 6)) message
      require (targetDispositions.contains (← cell correction 8)) message
      require (subkinds.contains (← cell correction 7)) message
      require (subkinds.contains (← cell correction 9)) message
      require (correction.extract 6 8 != correction.extract 8 10) "combined correction requires changed classification"
    else require (correction.extract 6 8 == correction.extract 8 10) "content amendment changes classification"
    let message := "content amendment page source mismatch"
    let some page := pages.index[← cell claim 3]? | throw <| IO.userError message
    require ((← cell page 1) == (← cell event 2)) message
    require ((← cell page 9) == pageOid) message
    require (validOid pageOid) message
    let message := "content amendment requires frozen old and new content OIDs"
    require (validOid oldOid && validOid newOid && oldOid.length == newOid.length) message
    require (oldOid != newOid) "content amendment is a no-op"
    let ordinal ← integer (← cell event 1)
    let historyOrder := if !history.contains claimId then historyOrder.push claimId else historyOrder
    let history := history.insert claimId ((history[claimId]?.getD #[]).push (ordinal,oldOid,newOid))
    pure (seen,owned,history,historyOrder))
    (({},{},{},#[]) : Std.HashSet String × Std.HashSet String ×
      Std.HashMap String (Array (Int × String × String)) × Array String)
  for correction in corrections.data do
    if contentActions.contains (← cell correction 5) then
      require (owned.contains (← cell correction 0)) "content amendment is missing its provenance row"
  for (name,column) in #[("claim-successors.tsv",2),("source-item-additions.tsv",2)] do
    for row in ← rows root name do
      require (!owned.contains (← cell row column)) "content amendment cannot introduce successors or source items"
  for claim in historyOrder do
    let entries := (history[claim]?.getD #[]).qsort fun a b =>
      a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
    for i in [:entries.size-1] do
      let previous := entries[i]!; let current := entries[i+1]!
      require (previous.1 != current.1 && previous.2.2 == current.2.1) "content amendment history chain is stale"
  let additions ← additionsStatic root
  return (amendments,additions)

/-- Check static ownership, classification, frozen OIDs and ordered history, preserving the public result. -/
def validateStatic (root : FilePath) : IO (Array Row) :=
  Prod.fst <$> validateContent root

/-- Validate one amended target, including its exact immutable metadata and refreshed vocabulary review. -/
private def targetTransition (project base current : FilePath) (event row : Row)
    (oldClaims claims oldPages pages : Keyed) : IO Unit := do
  let claimId ← cell row 3
  let oldOid ← cell row 4; let newOid ← cell row 5; let pageOid ← cell row 6
  let message := "content amendment does not target a frozen source claim"
  let some old := oldClaims.index[claimId]? | throw <| IO.userError message
  let some claim := claims.index[claimId]? | throw <| IO.userError message
  require ((← cell old 1) == (← cell event 2)) message
  let corrections ← keyed current "claim-corrections.tsv"
  let correction ← key corrections (← cell row 2)
  let combined := (← cell correction 5) == "amend_and_reclassify"
  if combined then
    for record in #[old,claim] do
      let message := "combined correction requires an active formalization target"
      require (record.size == 15) message
      require (targetDispositions.contains (← cell record 5)) message
      require (record.extract 9 record.size == #["NONE","NONE","false","NONE","NONE","NONE"]) message
    let message := "combined correction classification does not match claim transition"
    require (correction.extract 6 8 == old.extract 5 7) message
    require (correction.extract 8 10 == claim.extract 5 7) message
  else
    let message := "content amendment requires an active formalization target"
    require ((← cell old 11) == "false") message
    require ((← cell old 5) != "out_of_scope") message
  let allowed := if combined then #[5,6,7,8] else #[7,8]
  let message := (if combined then "combined correction" else "content amendment") ++ " changed frozen claim identity or metadata"
  for i in [:min old.size claim.size] do
    if !allowed.contains i then require (old[i]! == claim[i]!) message
  require (old.size == claim.size) message
  let oldPageId ← cell old 3; let pageId ← cell claim 3
  if combined then
    let sourceId ← cell event 2
    let oldSources ← keyed base "sources.tsv"
    let sources ← keyed current "sources.tsv"
    let message := "combined correction source record changed or is not frozen"
    let some source := sources.index[sourceId]? | throw <| IO.userError message
    require (oldSources.index[sourceId]? == some source) message
    require (validOid (← cell source 14)) message
    require (validOid (← cell source 15)) message
    require ((← cell source 14).length == (← cell source 15).length) message
    let oldPage ← key oldPages oldPageId
    require ((← cell oldPage 9) == pageOid) "content amendment page source mismatch"
    let page ← key pages pageId
    require ((← cell page 9) == pageOid) "content amendment page source mismatch"
    require (oldPage == page) "combined correction page record changed"
  let content ← cell claim 7
  require (!contentless content) "contentless content amendment surrogate"
  let oldContent ← cell old 7
  require (oldContent != content) "content amendment is a no-op"
  require ((← blob project oldContent) == oldOid) "content amendment old content OID is stale"
  let priorOid ← cell old 8
  require (priorOid == "PENDING" || priorOid == oldOid) "content amendment old content OID is stale"
  require ((← blob project content) == newOid) "content amendment new content OID is stale"
  require ((← cell claim 8) == newOid) "content amendment new content OID is stale"
  require ((← cell (← key oldPages oldPageId) 9) == pageOid) "content amendment page source mismatch"
  require ((← cell (← key pages pageId) 9) == pageOid) "content amendment page source mismatch"
  noRelations base current claimId "content amendment target already has skeleton or axiom relations"
  let oldUses ← selectRows (← rows base "claim-vocabulary.tsv") fun record => return (← cell record 0) == claimId
  let newUses ← selectRows (← rows current "claim-vocabulary.tsv") fun record => return (← cell record 0) == claimId
  require (oldUses.qsort (· < ·) == newUses.qsort (· < ·)) "content amendment changed vocabulary use"
  let oldReviews ← selectRows (← rows base "claim-vocabulary-review.tsv") fun record => return (← cell record 0) == claimId
  let newReviews ← selectRows (← rows current "claim-vocabulary-review.tsv") fun record => return (← cell record 0) == claimId
  let message := "content amendment lacks its refreshed vocabulary review"
  require (oldReviews.size == 1 && newReviews.size == 1) message
  require (oldReviews[0]!.extract 0 2 == newReviews[0]!.extract 0 2) message
  require ((← cell newReviews[0]! 2) == (← cell event 4)) message
  if combined then
    let invariants ← keyed current "source-invariants.tsv"
    let some invariant := invariants.index[← cell event 2]? |
      throw <| IO.userError "combined correction lacks its event invariant review"
    require ((← cell invariant 7) == (← cell event 4)) "combined correction lacks its event invariant review"

/-- The explicit project preserves the original Git hash-object working directory for typed callers. -/
def validateTransitionAt (project base current : FilePath) (eventId : String) : IO Unit := do
  let (amendments,additions) ← validateContent current
  let oldAmendments ← rows base "claim-content-amendments.tsv" true
  let oldById ← oldAmendments.foldlM (fun index row => do pure (index.insert (← cell row 0) row))
    ({} : Std.HashMap String Row)
  let currentById ← amendments.foldlM (fun index row => do pure (index.insert (← cell row 0) row))
    ({} : Std.HashMap String Row)
  let oldPath := base / "registry/claim-content-amendments.tsv"
  if ← oldPath.pathExists then
    let before ← IO.FS.readBinFile oldPath
    let after ← IO.FS.readBinFile (current / "registry/claim-content-amendments.tsv")
    require (before.size ≤ after.size && after.extract 0 before.size == before) "historical content amendment drift"
  for (identifier,row) in oldById do
    require (currentById[identifier]? == some row) "historical content amendment drift"
  let fresh ← selectRows amendments fun row => return !oldById.contains (← cell row 0)
  for row in fresh do require ((← cell row 1) == eventId) "content amendment belongs to another event"
  let events ← keyed current "correction-events.tsv"
  let event ← key events eventId
  let expected ← (← rows current "claim-corrections.tsv").foldlM (fun expected row => do
    if (← cell row 1) == eventId then
      if contentActions.contains (← cell row 5) then return expected.insert (← cell row 0)
    pure expected) ({} : Std.HashSet String)
  let actual ← fresh.foldlM (fun actual row => do pure (actual.insert (← cell row 2)))
    ({} : Std.HashSet String)
  require (actual.size == expected.size && expected.toArray.all actual.contains)
    "content amendment provenance is not new for this event"
  additionsTransition project base current event additions
  if fresh.isEmpty then return
  let oldClaims ← keyed base "claims.tsv"
  let claims ← keyed current "claims.tsv"
  let oldPages ← keyed base "pages.tsv"
  let pages ← keyed current "pages.tsv"
  let sourceId ← cell event 2
  preR4 base oldClaims sourceId "content amendment"
  preR4 current claims sourceId "content amendment"
  for row in fresh do targetTransition project base current event row oldClaims claims oldPages pages

/-- Standalone API inherits the current directory, as the original helper's hash subprocess did. -/
def validateTransition (base current : FilePath) (event : String) : IO Unit := do
  validateTransitionAt (← IO.currentDir) base current event

/-- The two mutually exclusive, explicitly rooted helper modes. -/
private inductive Mode where
  | static (root : FilePath)
  | transition (base current : FilePath) (event : String)
  | help

/-- Argparse treats negative decimal literals as values, while other dash-prefixed tokens are options. -/
private def optionToken (value : String) : Bool :=
  Checker.Text.optionToken value

/-- Carry the unconsumed arguments and last same-mode option explicitly, preserving help's early return. -/
private partial def parseRemaining (args : List String) (selected : Option Mode) : Except String Mode := do
  match args with
  | [] => match selected with
    | some mode => return mode
    | none => throw "one of the arguments --static --transition is required"
  | arg :: remaining =>
    if arg == "-h" || arg == "--help" then return .help
    let pieces := arg.splitOn "="
    let option := pieces.head!
    let explicit := if pieces.length > 1 then some (String.intercalate "=" pieces.tail!) else none
    let candidates := #["--static","--transition","--help"].filter (fun name =>
      option.startsWith "--" && name.startsWith option)
    if candidates.size != 1 then throw ("unrecognized arguments: " ++ arg)
    let option := candidates[0]!
    if option == "--help" then
      if explicit.isSome then throw "argument -h/--help: ignored explicit argument"
      return .help
    if option == "--static" then
      if let some (.transition ..) := selected then throw "argument --static: not allowed with argument --transition"
      if explicit.isNone && (remaining.isEmpty || optionToken remaining.head!) then
        throw "argument --static: expected one argument"
      let value := explicit.getD (remaining.headD "")
      parseRemaining (if explicit.isNone then remaining.tail! else remaining) (some (.static (FilePath.mk value)))
    else
      if let some (.static _) := selected then throw "argument --transition: not allowed with argument --static"
      if explicit.isSome then throw "argument --transition: expected 3 arguments"
      let values := remaining.take 3
      if values.length != 3 || values.any optionToken then
        throw "argument --transition: expected 3 arguments"
      parseRemaining (remaining.drop 3) (some (.transition (FilePath.mk values[0]!) (FilePath.mk values[1]!) values[2]!))

/-- Parse the original mode arguments, including help, repeated same-mode options and unique long prefixes. -/
private def parseArgs (args : List String) : Except String Mode := parseRemaining args none

/-- Native replacement entry preserves helper diagnostics and success text for all existing callers. -/
def entry (project : FilePath) (args : List String) : IO Unit := do
  try
    match ← IO.ofExcept (parseArgs args) with
    | .help => IO.println "usage: content (--static ROOT | --transition BASE CURRENT EVENT)\n\nValidate reviewed content amendments and omitted-claim creation provenance."
    | .static root =>
      discard <| Checker.RegistryIO.load root (← Checker.RegistryIO.currentProfile project root) #["sources"]
      discard <| validateStatic root
      IO.println "check-content-amendments: ok"
    | .transition base current event =>
      discard <| Checker.RegistryIO.load current (← Checker.RegistryIO.currentProfile project current) #["sources"]
      validateTransitionAt project base current event
      IO.println "check-content-amendments: ok"
  catch error => throw <| IO.userError s!"check-content-amendments: {error}"

/-- Preserve usage status two separately from validation status one without bypassing caller cleanup. -/
def cli (project : FilePath) (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
    IO.eprintln "usage: content (--static ROOT | --transition BASE CURRENT EVENT)"
    IO.eprintln s!"content: error: {message}"
    return 2
  | .ok _ =>
    try
      entry project args
      return 0
    catch error =>
      IO.eprintln s!"{error}"
      return 1

end Checker.Content
