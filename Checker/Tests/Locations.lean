import Checker.Locations
import Checker.Corrections
import Checker.TestSupport

/-! Independent finite fixtures for reviewed, same-page locator maintenance. -/
namespace Checker.Tests.Locations
open Checker.TestSupport

/-- Exact synthetic TSV fields retain the production validators' column numbering. -/
private abbrev Row := Array String

/-- Both revisions and their review-owned location history, without filesystem fixtures. -/
private structure Fixture where
  oldClaims : Array Row
  claims : Array Row
  oldItems : Array Row
  items : Array Row
  oldRelations : Array Row
  relations : Array Row
  pages : Array Row
  events : Array Row
  reviews : Array Row
  corrections : Array Row
  oldAmendments : Array Row := #[]
  amendments : Array Row

/-- Three distinct singleton owners exercise one source-local event. -/
private def ids : Array String := #["0001", "0002", "0003"]

/-- The historical locator preserves a fixed page, print page and section. -/
private def oldLocator (suffix : String) : String :=
  "PDF p. 10; print p. 1; §2.1; historical paragraph " ++ suffix

/-- The refined locator changes only its paragraph-level description. -/
private def newLocator (suffix : String) : String :=
  "PDF p. 10; print p. 1; §2.1; reviewed equation-adjacent paragraph " ++ suffix

/-- A synthetic active assertion has frozen content, order and provenance fields. -/
private def claim (suffix locator : String) : Row :=
  #["CL-TEST-" ++ suffix, "TEST", "000010." ++ suffix, "PG-TEST-0010", locator,
    "assertion", "remark", "Retained source assertion " ++ suffix,
    "1111111111111111111111111111111111111111", "NONE", "NONE", "false", "NONE", "NONE", "NONE"]

/-- A synthetic singleton item preserves all non-locator metadata. -/
private def item (suffix locator : String) : Row :=
  #["IT-TEST-" ++ suffix, "TEST", "000010." ++ suffix, "PG-TEST-0010", "unlabeled",
    "NONE", "NONE", locator, "Chapter 02", "chapter-02", "ORIGINAL-REVIEW"]

/-- Each amendment has its own closed source-location readiness review. -/
private def review (suffix : String) (event : String := "EVENT-ONE") : Row :=
  #["NR-TEST-" ++ suffix, event, suffix, "CL-TEST-" ++ suffix, "source_location_readiness",
    "amend_location", "closed", "reviewed-same-page-location", "INDEPENDENT-REVIEW"]

/-- Location ownership retains the original classification on both sides. -/
private def correction (suffix : String) (event : String := "EVENT-ONE") : Row :=
  #["CC-TEST-" ++ suffix, event, suffix, "NR-TEST-" ++ suffix, "CL-TEST-" ++ suffix,
    "amend_location", "assertion", "remark", "assertion", "remark"]

/-- A row binds exact old/new claim and item locator bytes to one correction. -/
private def amendment (suffix : String) : Row :=
  #["LA-TEST-" ++ suffix, "EVENT-ONE", "CC-TEST-" ++ suffix, "CL-TEST-" ++ suffix,
    "IT-TEST-" ++ suffix, oldLocator suffix, newLocator suffix,
    oldLocator suffix, newLocator suffix, "INDEPENDENT-REVIEW"]

/-- Three separate singleton pairs share one page; every non-locator byte stays fixed. -/
private def initial : Fixture :=
  let relations := ids.map fun suffix => #["IT-TEST-" ++ suffix, "1", "CL-TEST-" ++ suffix]
  { oldClaims := ids.map fun suffix => claim suffix (oldLocator suffix)
    claims := ids.map fun suffix => claim suffix (newLocator suffix)
    oldItems := ids.map fun suffix => item suffix (oldLocator suffix)
    items := ids.map fun suffix => item suffix (newLocator suffix)
    oldRelations := relations, relations := relations
    pages := #[#["PG-TEST-0010", "TEST", "000010", "1", "10", "§2.1", "body",
      "complete", "complete", "2222222222222222222222222222222222222222"]]
    events := #[#["EVENT-ONE", "1", "TEST", "base-one", "INDEPENDENT-REVIEW"]]
    reviews := ids.map fun suffix => review suffix
    corrections := ids.map fun suffix => correction suffix
    amendments := ids.map amendment }

/-- Modify one explicit zero-based field in a bounded synthetic table. -/
private def field (rows : Array Row) (row column : Nat) (value : String) : Array Row :=
  rows.set! row (rows[row]!.set! column value)

/-- Invoke the complete production history and endpoint validator. -/
private def history (f : Fixture) : IO Unit :=
  Checker.Locations.validateHistory f.claims f.items f.pages f.relations
    f.events f.reviews f.corrections f.amendments

/-- Invoke the production field-ownership validator on both revisions. -/
private def transition (f : Fixture) (event : String := "EVENT-ONE") : IO Unit :=
  Checker.Locations.validateTransition f.oldClaims f.oldItems f.oldRelations f.claims f.items
    f.relations f.oldAmendments f.amendments event

/-- The current ledger header is part of the exact-byte prefix contract. -/
private def ledgerHeader : String :=
  "location_amendment_id\tevent_id\tcorrection_id\tclaim_id\titem_id\told_claim_locator\tnew_claim_locator\told_item_locator\tnew_item_locator\treview_ref\n"

/-- Serialize synthetic ledger rows with one LF per record. -/
private def ledgerText (rows : Array Row) : String :=
  ledgerHeader ++ String.join (rows.toList.map fun row => String.intercalate "\t" row.toList ++ "\n")

/-- Exercise the production exact-byte prefix guard independently of parsed location rows. -/
private def freeze (before after : String) : IO Unit :=
  let snapshot := fun text =>
    let files := ({} : Std.HashMap String String).insert "registry/claim-location-amendments.tsv" text
    ({ files := files } : Checker.BaseDiff.Snapshot)
  Checker.Corrections.freezeLedger (snapshot before) (snapshot after) "claim-location-amendments" "EVENT-TWO" 2

/-- A first ledger starts from actual historical absence and admits only its current event's rows. -/
private def firstLedger (rows : Array Row) : IO Unit :=
  let current : Checker.BaseDiff.Snapshot :=
    { files := ({} : Std.HashMap String String).insert "registry/claim-location-amendments.tsv" (ledgerText rows) }
  Checker.Corrections.freezeLedger ({} : Checker.BaseDiff.Snapshot) current
    "claim-location-amendments" "EVENT-ONE" 2

/-- A later event owns one new link, retaining every earlier amendment and pair. -/
private def later : Fixture :=
  let f := initial
  let tail := "PDF p. 10; print p. 1; §2.1; second reviewed location"
  let readiness := (review "0001" "EVENT-TWO").set! 0 "NR-TEST-0004"
  let action := ((correction "0001" "EVENT-TWO").set! 0 "CC-TEST-0004").set! 3 "NR-TEST-0004"
  let change := #["LA-TEST-0004", "EVENT-TWO", "CC-TEST-0004", "CL-TEST-0001", "IT-TEST-0001",
    newLocator "0001", tail, newLocator "0001", tail, "INDEPENDENT-REVIEW"]
  { f with
    oldClaims := f.claims
    oldItems := f.items
    oldAmendments := f.amendments
    claims := field f.claims 0 4 tail
    items := field f.items 0 7 tail
    events := f.events.push #["EVENT-TWO", "2", "TEST", "base-two", "INDEPENDENT-REVIEW"]
    reviews := f.reviews.push readiness
    corrections := f.corrections.push action
    amendments := f.amendments.push change }

/-- Identity negatives must reach the production identity rejection. -/
private def identityDiagnostic := "invalid source-location amendment identity"
/-- Ownership negatives must reach the production review rejection. -/
private def ownerDiagnostic := "source-location amendment lacks its unique closed event review"
/-- Source and membership negatives must reach their own rejection. -/
private def membershipDiagnostic := "source-location amendment changes its source, page or singleton membership"
/-- Page and section negatives must reach the frozen-prefix rejection. -/
private def prefixDiagnostic := "source-location amendment changes its frozen page or section prefix"
/-- Non-locator drift must reach the explicit ownership rejection. -/
private def transitionDiagnostic := "source-location transition changes unowned fields or its recorded old values"

/-- A case is executed directly, so its label, polarity and required diagnostic are the roster. -/
private structure Case where
  label : String
  positive : Bool := false
  action : IO Unit
  diagnostic : String := ""

/-- History cases keep each altered premise separate from the valid baseline. -/
private def historyCases : Array Case :=
  let f := initial
  #[
    { label := "locations-three-reviewed-pairs", positive := true, action := do history f; transition f },
    { label := "locations-first-ledger-from-absent-snapshot", positive := true, action := firstLedger f.amendments },
    { label := "locations-first-ledger-foreign-owner", action := firstLedger (field f.amendments 0 1 "OTHER-EVENT"),
      diagnostic := "historical correction ledger drift" },
    { label := "locations-unchanged-empty-history", positive := true, action := do
      let unchanged := { f with
        claims := f.oldClaims
        items := f.oldItems
        events := #[]
        reviews := #[]
        corrections := #[]
        amendments := #[] }
      history unchanged; transition unchanged },
    { label := "locations-later-exact-chain", positive := true, action := do
      history later; transition later "EVENT-TWO"
      freeze (ledgerText f.amendments) (ledgerText later.amendments) },
    { label := "locations-malformed-la-prefix", action := history { f with
      amendments := field f.amendments 0 0 "CA-TEST-0001" }, diagnostic := identityDiagnostic },
    { label := "locations-malformed-la-decimal", action := history { f with
      amendments := field f.amendments 0 0 "LA-TEST-001x" }, diagnostic := identityDiagnostic },
    { label := "locations-malformed-row-width", action := history { f with
      amendments := f.amendments.set! 0 (f.amendments[0]!.pop) }, diagnostic := identityDiagnostic },
    { label := "locations-duplicate-amendment-id", action := history { f with
      amendments := field f.amendments 1 0 "LA-TEST-0001" }, diagnostic := identityDiagnostic },
    { label := "locations-wrong-owner", action := history { f with
      amendments := field f.amendments 0 2 "CC-TEST-0002" }, diagnostic := ownerDiagnostic },
    { label := "locations-wrong-action", action := history { f with
      corrections := field f.corrections 0 5 "amend_content" }, diagnostic := ownerDiagnostic },
    { label := "locations-action-classification-drift", action := history { f with
      corrections := field f.corrections 0 8 "definition" }, diagnostic := ownerDiagnostic },
    { label := "locations-open-review", action := history { f with
      reviews := field f.reviews 0 6 "open" }, diagnostic := ownerDiagnostic },
    { label := "locations-wrong-review-scope", action := history { f with
      reviews := field f.reviews 0 4 "exact_statement_readiness" }, diagnostic := ownerDiagnostic },
    { label := "locations-wrong-review-reference", action := history { f with
      amendments := field f.amendments 0 9 "OTHER-REVIEW" }, diagnostic := ownerDiagnostic },
    { label := "locations-unknown-event", action := history { f with
      amendments := field f.amendments 0 1 "UNKNOWN-EVENT" }, diagnostic := "source-location event is unknown" },
    { label := "locations-wrong-source", action := history { f with
      events := field f.events 0 2 "OTHER" }, diagnostic := membershipDiagnostic },
    { label := "locations-item-page-drift", action := history { f with
      items := field f.items 0 3 "PG-TEST-0011" }, diagnostic := membershipDiagnostic },
    { label := "locations-nonsingleton-membership", action := history { f with
      relations := f.relations.push #["IT-TEST-0001", "2", "CL-OTHER-0001"] }, diagnostic := membershipDiagnostic },
    { label := "locations-membership-position-drift", action := history { f with
      relations := field f.relations 0 1 "2" }, diagnostic := membershipDiagnostic },
    { label := "locations-physical-page-prefix-drift", action := history { f with
      amendments := field f.amendments 0 6 "PDF p. 11; print p. 1; §2.1; new location" }, diagnostic := prefixDiagnostic },
    { label := "locations-printed-page-prefix-drift", action := history { f with
      amendments := field f.amendments 0 8 "PDF p. 10; print p. 2; §2.1; new location" }, diagnostic := prefixDiagnostic },
    { label := "locations-section-prefix-drift", action := history { f with
      amendments := field f.amendments 0 6 "PDF p. 10; print p. 1; §2.2; new location" }, diagnostic := prefixDiagnostic },
    { label := "locations-noop-amendment", action := history { f with
      amendments := field f.amendments 0 6 (oldLocator "0001") }, diagnostic := prefixDiagnostic },
    { label := "locations-missing-amendment-owner-pair", action := history { f with
      amendments := f.amendments.extract 0 2 }, diagnostic := "source-location corrections and amendments are not bijective" },
    { label := "locations-claim-endpoint-drift", action := history { f with
      claims := field f.claims 0 4 (oldLocator "0001") }, diagnostic := "source-location current endpoint differs from its history" },
    { label := "locations-item-endpoint-drift", action := history { f with
      items := field f.items 0 7 (oldLocator "0001") }, diagnostic := "source-location current endpoint differs from its history" },
    { label := "locations-broken-later-chain", action := history { later with
      amendments := field later.amendments 3 5 (oldLocator "0001") }, diagnostic := "source-location amendment chain is broken" },
    { label := "locations-event-order-regression", action := history { later with
      amendments := #[later.amendments[3]!, later.amendments[0]!, later.amendments[1]!, later.amendments[2]!] },
      diagnostic := ownerDiagnostic }
  ]

/-- Transition cases isolate locator ownership and immutable-prefix failures. -/
private def transitionCases : Array Case :=
  let f := initial
  #[
    { label := "locations-no-ledger-for-claim-change", action := transition { f with amendments := #[] },
      diagnostic := "claim locator changed without an owned source-location amendment" },
    { label := "locations-no-ledger-for-item-change", action := transition { f with
      claims := f.oldClaims, amendments := #[] },
      diagnostic := "item locator changed without an owned source-location amendment" },
    { label := "locations-only-claim-updated", action := transition { f with items := f.oldItems },
      diagnostic := transitionDiagnostic },
    { label := "locations-only-item-updated", action := transition { f with claims := f.oldClaims },
      diagnostic := transitionDiagnostic },
    { label := "locations-body-drift", action := transition { f with
      claims := field f.claims 0 7 "Changed body" }, diagnostic := transitionDiagnostic },
    { label := "locations-content-oid-drift", action := transition { f with
      claims := field f.claims 0 8 "3333333333333333333333333333333333333333" }, diagnostic := transitionDiagnostic },
    { label := "locations-claim-page-drift", action := transition { f with
      claims := field f.claims 0 3 "PG-TEST-0011" }, diagnostic := transitionDiagnostic },
    { label := "locations-claim-order-drift", action := transition { f with
      claims := field f.claims 0 2 "000010.9999" }, diagnostic := transitionDiagnostic },
    { label := "locations-item-order-drift", action := transition { f with
      items := field f.items 0 2 "000010.9999" }, diagnostic := transitionDiagnostic },
    { label := "locations-false-recorded-old-locator", action := transition { f with
      amendments := field f.amendments 0 5 "PDF p. 10; print p. 1; §2.1; not the original" },
      diagnostic := transitionDiagnostic },
    { label := "locations-old-membership-drift", action := transition { f with
      oldRelations := field f.oldRelations 0 2 "CL-OTHER-0001" }, diagnostic := transitionDiagnostic },
    { label := "locations-foreign-fresh-event", action := transition f "EVENT-TWO", diagnostic := transitionDiagnostic },
    { label := "locations-old-ledger-bytes-rewritten", action :=
      freeze (ledgerText f.amendments) (ledgerText (field later.amendments 0 9 "REWRITTEN")),
      diagnostic := "historical correction ledger drift" },
    { label := "locations-old-ledger-row-dropped", action :=
      freeze (ledgerText f.amendments) (ledgerText (later.amendments.extract 1 4)),
      diagnostic := "historical correction ledger drift" },
    { label := "locations-foreign-ledger-append", action :=
      freeze (ledgerText f.amendments) (ledgerText (field later.amendments 3 1 "FOREIGN-EVENT")),
      diagnostic := "historical correction ledger drift" }
  ]

/-- Add the independent location cases to the existing correction group's counters and roster. -/
def run (ctx : Context) : IO Unit := do
  let cases := historyCases ++ transitionCases
  ensure ((cases.map (·.label)).toList.eraseDups.length == cases.size) "duplicate source-location case label"
  for test in cases do
    expectAction ctx test.label test.positive test.action test.diagnostic "source-location"
  IO.println s!"test-source-locations: ok ({cases.size} cases; {(cases.filter (·.positive)).size} positive, {(cases.filter (! ·.positive)).size} negative)"

end Checker.Tests.Locations
