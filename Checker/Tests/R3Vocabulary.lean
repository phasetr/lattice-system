import Checker.BaseDiff

/-! Finite admission controls for pre-freeze R3 reviews.
These tests exercise registry history, not declaration existence, semantic OIDs or R4 consumption;
the entry route owns native coverage and fresh-environment inspection separately.
-/
namespace Checker.Tests.R3Vocabulary
open Checker.CheckAll Checker.BaseDiff

private abbrev Row := Array String

private def target : String := "CL-TEST-0001"
private def secondary : String := "CL-TEST-0002"
private def established : String := "CL-TEST-0003"
private def oldVocabulary : String := "VO-LS-0001"
private def newVocabulary : String := "VO-LS-0002"
private def fingerprint : String := "1111111111111111111111111111111111111111"
private def diagnostic : String := "invalid pre-freeze R3 vocabulary review advance"

private def futureTables : Array String := #["slices", "dependencies", "bindings", "claim-context",
  "axioms", "claim-axioms", "statement-modules", "statement-imports"]

private def ledgers : Array String := #["correction-events", "claim-normalization-reviews",
  "claim-corrections", "claim-successors", "source-item-additions", "claim-content-amendments",
  "claim-location-amendments"]

private def path (stem : String) : String := "registry/" ++ stem ++ ".tsv"

/-- Schema names come from the production table owner; no fixture invents extra columns. -/
private def tableHeader (stem : String) : IO String :=
  match Checker.CheckAll.Registry.headers.find? (·.1 == stem) with
  | some (_, header) => pure header
  | none => throw <| IO.userError ("missing registered test schema: " ++ stem)

private def tableText (header : String) (rows : Array Row) : String :=
  header ++ "\n" ++ String.join (rows.toList.map fun row => String.intercalate "\t" row.toList ++ "\n")

/-- Pure snapshots carry the documented logical tables directly, without asserting physical compact IO. -/
private def put (snapshot : Snapshot) (stem : String) (rows : Array Row) : IO Snapshot := do
  let header ← tableHeader stem
  return { snapshot with
    files := snapshot.files.insert (path stem) (tableText header rows)
    views := snapshot.views.erase (path stem) }

private def source : Row := #["TEST", "TR-TEST", "1", "book", "TEST", "Reviewed synthetic source",
  "Test Author", "2026", "test-edition", "none", "NONE", "NONE", "test", "synthetic.pdf",
  fingerprint, fingerprint, "frozen"]

private def progress (stage : String := "vocabulary_reviewed") : Array Row :=
  #[#["TEST", stage, "LIFECYCLE-INDEPENDENT-REVIEW"]]

private def claim (id order : String) : Row :=
  #[id, "TEST", order, "PG-TEST-0001", "PDF p. 1; print p. 1; §1; definition paragraph",
    "definition", "definition", "A local definition in the registered source.", fingerprint,
    "NONE", "NONE", "false", "NONE", "NONE", "NONE"]

private def claims : Array Row := #[claim target "000001.0001", claim secondary "000001.0002",
  claim established "000001.0003"]

private def beforeReviews : Array Row := #[
  #[target, "mathlib_only", "OLD-TARGET-REVIEW"],
  #[secondary, "mathlib_only", "OLD-SECONDARY-REVIEW"],
  #[established, "project_vocabulary", "ESTABLISHED-REVIEW"]]

private def afterReviews : Array Row := beforeReviews.set! 0
  #[target, "project_vocabulary", "FRESH-TARGET-REVIEW"]

private def vocabulary (id declaration : String) : Row :=
  #[id, declaration, "LatticeSystem.Vocabulary.Test", "definition", "primary", "NONE",
    fingerprint, fingerprint, "operator_algebra", "local_operation"]

private def oldDeclaration : Row := vocabulary oldVocabulary "LatticeSystem.existingLocalDefinition"
private def newDeclaration : Row := vocabulary newVocabulary "LatticeSystem.newLocalDefinition"
private def oldUses : Array Row := #[#[established, oldVocabulary]]
private def newUses : Array Row := oldUses.push #[target, newVocabulary]

private structure Fixture where
  before : Snapshot
  current : Snapshot

/-- One reviewed claim advances while an unrelated registered declaration and use remain present. -/
private def fixture : IO Fixture := do
  let before ← (#["phase", "sources", "source-progress", "claims", "claim-vocabulary-review",
    "vocabulary", "claim-vocabulary"] ++ futureTables ++ ledgers).foldlM
      (fun snapshot stem => put snapshot stem #[]) ({} : Snapshot)
  let before := { before with files := before.files.insert (path "phase") "phase\nvocabulary\n" }
  let before ← put before "sources" #[source]
  let before ← put before "source-progress" (progress)
  let before ← put before "claims" claims
  let before ← put before "claim-vocabulary-review" beforeReviews
  let before ← put before "vocabulary" #[oldDeclaration]
  let before ← put before "claim-vocabulary" oldUses
  let current ← put before "claim-vocabulary-review" afterReviews
  let current ← put current "vocabulary" #[oldDeclaration, newDeclaration]
  let current ← put current "claim-vocabulary" newUses
  return { before, current }

private def both (f : Fixture) (stem : String) (rows : Array Row) : IO Fixture := do
  return { before := ← put f.before stem rows, current := ← put f.current stem rows }

private def accepted (f : Fixture) (expected : Array String := #[target]) : IO Unit := do
  require ((← vocabularyReviewAdvances f.before f.current) == expected) "wrong admitted R3 claim identities or order"

/-- A malformed admission must reach this specific history guard, rather than any exception. -/
private def rejected (f : Fixture) : IO Unit := do
  let failure ← try
    discard <| vocabularyReviewAdvances f.before f.current
    pure (none : Option String)
    catch error => pure (some error.toString)
  require (failure.any fun text => (text.splitOn diagnostic).length > 1) "R3 review guard did not reject its boundary"

private def noChangeControl : IO Unit := do
  let minimal ← put {} "claim-vocabulary-review" beforeReviews
  accepted { before := minimal, current := minimal } #[]

private def rawAbsenceControl (f : Fixture) : IO Unit := do
  let erase := fun snapshot => ledgers.foldl (fun (snapshot : Snapshot) stem =>
    {snapshot with files := snapshot.files.erase (path stem)}) snapshot
  accepted { before := erase f.before, current := erase f.current }

private def twoAdmissionControl (f : Fixture) : IO Unit := do
  let reviews := #[beforeReviews[2]!, #[secondary, "project_vocabulary", "FRESH-SECONDARY-REVIEW"], afterReviews[0]!]
  let current ← put f.current "claim-vocabulary-review" reviews
  let current ← put current "claim-vocabulary" (newUses.push #[secondary, newVocabulary])
  let admitted ← vocabularyReviewAdvances f.before current
  require (admitted.size == 2 && admitted.toList.eraseDups.length == 2 &&
    admitted.contains target && admitted.contains secondary) "wrong two-claim R3 admission set"

/-- These are schema-shaped artifacts, not arbitrary strings used to provoke parse failures.
    Their appearance alone is forbidden by the pre-R4 admission boundary. -/
private def artifact (stem : String) : IO Row :=
  match stem with
  | "slices" => pure #["SL-TEST-0001", "1", target]
  | "dependencies" => pure #[secondary, "requires", target, "source-definition"]
  | "bindings" => pure #[target, "LatticeSystem.Statements.Test.definition", "NONE",
      "LatticeSystem.Statements.Test", "definition", "definition_value", fingerprint, fingerprint,
      "definitional", "NONE", "NONE", "NONE", "NONE", "NONE", "R4-INDEPENDENT-REVIEW"]
  | "claim-context" => pure #[secondary, "1", target, "term_reference", "inherited", "R4-INDEPENDENT-REVIEW"]
  | "axioms" => pure #["AX-TEST-0001", "LatticeSystem.Axioms.State.testState", "LatticeSystem.Axioms.State",
      "state", "PDF p. 1; §1", "state-existence", "revisit-when-constructed", fingerprint]
  | "claim-axioms" => pure #[target, "AX-TEST-0001"]
  | "statement-modules" => pure #["LatticeSystem.Statements.Test", "LatticeSystem/Statements/Test.lean", "leaf"]
  | "statement-imports" => pure #["LatticeSystem.Statements.Test", "1", "Mathlib", "false", "false", "false"]
  | _ => throw <| IO.userError "unknown R4 test artifact"

private structure Control where
  label : String
  action : IO Unit

private def controls (f : Fixture) : Array Control := #[
  ⟨"r3-vocabulary-unchanged-minimal-fastpath", noChangeControl⟩,
  ⟨"r3-vocabulary-new-definition-admission", accepted f⟩,
  ⟨"r3-vocabulary-phase-without-terminal-lf", do
    let phase := "phase\nvocabulary"
    accepted {
      before := {f.before with files := f.before.files.insert (path "phase") phase}
      current := {f.current with files := f.current.files.insert (path "phase") phase} }⟩,
  ⟨"r3-vocabulary-true-ledger-absence", rawAbsenceControl f⟩,
  ⟨"r3-vocabulary-two-admission-identity-set", twoAdmissionControl f⟩,
  ⟨"r3-vocabulary-changed-phase", rejected {f with current :=
    {f.current with files := f.current.files.insert (path "phase") "phase\nskeleton\n"}}⟩,
  ⟨"r3-vocabulary-invalid-lifecycle", do rejected (← both f "source-progress" (progress "unknown"))⟩,
  ⟨"r3-vocabulary-already-skeleton-frozen", do rejected (← both f "source-progress" (progress "skeleton_frozen"))⟩,
  ⟨"r3-vocabulary-lifecycle-review-drift", do
    let current ← put f.current "source-progress" #[#["TEST", "vocabulary_reviewed", "DIFFERENT-LIFECYCLE-REVIEW"]]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-source-identity-drift", do
    let current ← put f.current "sources" #[source.set! 5 "A different source title"]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-source-claim-body-drift", do
    let current ← put f.current "claims" (claims.set! 0 (claims[0]!.set! 7 "A different source definition."))
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-excluded-target", do
    rejected (← both f "claims" (claims.set! 0 (claims[0]!.set! 5 "out_of_scope")))⟩,
  ⟨"r3-vocabulary-historical-target", do
    rejected (← both f "claims" (claims.set! 0 (claims[0]!.set! 11 "true")))⟩,
  ⟨"r3-vocabulary-same-review-reference", do
    let current ← put f.current "claim-vocabulary-review"
      (afterReviews.set! 0 #[target, "project_vocabulary", "OLD-TARGET-REVIEW"])
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-placeholder-review-references", do
    for reference in #["NONE", "PENDING", "UNKNOWN"] do
      let current ← put f.current "claim-vocabulary-review"
        (afterReviews.set! 0 #[target, "project_vocabulary", reference])
      rejected {f with current}⟩,
  ⟨"r3-vocabulary-reference-owned-by-other-old-review", do
    let current ← put f.current "claim-vocabulary-review"
      (afterReviews.set! 0 #[target, "project_vocabulary", "OLD-SECONDARY-REVIEW"])
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-invalid-review-token", do
    let current ← put f.current "claim-vocabulary-review"
      (afterReviews.set! 0 #[target, "project_vocabulary", "not a token"])
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-reference-only-rewrite", do
    let current ← put f.current "claim-vocabulary-review"
      (beforeReviews.set! 0 #[target, "mathlib_only", "FRESH-TARGET-REVIEW"])
    let current ← put current "claim-vocabulary" oldUses
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-basis-downgrade", do
    let before ← put f.before "claim-vocabulary-review"
      (beforeReviews.set! 0 #[target, "project_vocabulary", "OLD-TARGET-REVIEW"])
    let before ← put before "claim-vocabulary" (oldUses.push #[target, oldVocabulary])
    let current ← put f.current "claim-vocabulary-review"
      (beforeReviews.set! 0 #[target, "mathlib_only", "FRESH-TARGET-REVIEW"])
    let current ← put current "claim-vocabulary" (oldUses.push #[target, oldVocabulary])
    rejected {before, current}⟩,
  ⟨"r3-vocabulary-unexpected-old-target-use", do
    let before ← put f.before "claim-vocabulary" (oldUses.push #[target, oldVocabulary])
    let current ← put f.current "claim-vocabulary" (newUses.push #[target, oldVocabulary])
    rejected {before, current}⟩,
  ⟨"r3-vocabulary-no-new-target-use", do
    let current ← put f.current "claim-vocabulary" oldUses
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-unknown-use-target", do
    let current ← put f.current "claim-vocabulary" (oldUses.push #[target, "VO-LS-9999"])
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-only-existing-declaration", do
    let current ← put f.current "claim-vocabulary" (oldUses.push #[target, oldVocabulary])
    let current ← put current "vocabulary" #[oldDeclaration]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-new-nondefinition-primary", do
    let current ← put f.current "vocabulary" #[oldDeclaration, newDeclaration.set! 3 "structure"]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-generated-projection-is-not-primary-definition", do
    let generated := newDeclaration.set! 3 "projection" |>.set! 4 "generated"
      |>.set! 5 oldVocabulary |>.set! 8 "generated" |>.set! 9 "inherited"
    let current ← put f.current "vocabulary" #[oldDeclaration, generated]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-unfrozen-definition-fingerprints", do
    for column in #[6, 7] do
      let current ← put f.current "vocabulary" #[oldDeclaration, newDeclaration.set! column "PENDING"]
      rejected {f with current}⟩,
  ⟨"r3-vocabulary-old-unrelated-use-must-survive", do
    let current ← put f.current "claim-vocabulary" #[#[target, newVocabulary]]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-each-raw-ledger-absence-is-observable", do
    for stem in ledgers do
      let before := {f.before with files := f.before.files.erase (path stem)}
      rejected {f with before}⟩,
  ⟨"r3-vocabulary-no-new-source-event", do
    let current ← put f.current "correction-events"
      #[#["SOURCE-REPAIR-TEST", "1", "TEST", fingerprint, "SOURCE-INDEPENDENT-REVIEW"]]
    rejected {f with current}⟩,
  ⟨"r3-vocabulary-each-r4-artifact-blocks-admission", do
    for stem in futureTables do
      let current ← put f.current stem #[← artifact stem]
      rejected {f with current}⟩]

/-- Add one callback per finite control to the established self-test group. -/
def run (check : Bool → String → IO Unit) : IO Unit := do
  let cases := controls (← fixture)
  require (cases.size == 30 && (cases.map (·.label)).toList.eraseDups.length == cases.size)
    "R3 vocabulary control roster changed"
  for control in cases do
    let success ← try control.action; pure true catch _ => pure false
    check success control.label

end Checker.Tests.R3Vocabulary
