import Checker.Tests.Fixtures

/-! Ordinary base-diff regression contracts over exact production and legacy registry snapshots. -/
namespace Checker.Tests.BaseDiff
open System Checker.TestSupport Checker.Tests.Fixtures

/-- The expanded statement-binding schema whose semantic proof value is independently monotone. -/
def bindingHeader : String := "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref"

/-- A populated binding with separately frozen type, statement value and discharged proof value. -/
def bindingRow : String := "CL-TASAKI2020-0001\tLatticeSystem.Claims.Front.statement0001\tLatticeSystem.Claims.Front.claim0001\tLatticeSystem.Claims.Front\tdefinition\tproof_proposition\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tproof_stub\ttheorem\tcccccccccccccccccccccccccccccccccccccccc\tdddddddddddddddddddddddddddddddddddddddd\tNONE\tNONE\tRUNTIME-REVIEW"

/-- The original historical binding schema that may migrate only when empty. -/
def oldBindingHeader : String := "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_oid\tnonvacuity_decl"

/-- The current source-axiom schema with a separately frozen type identity. -/
def axiomHeader : String := "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid"

/-- A source-axiom record whose type identity is independently frozen. -/
def axiomRow : String := "AX-RUNTIME-0001\tLatticeSystem.Axioms.State.fixture\tLatticeSystem.Axioms.State\tstate\tfixture\tfixture\treopen\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

/-- The historical source-axiom schema accepted only as an empty migration input. -/
def oldAxiomHeader : String := "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition"

/-- Clone only registered corpus bytes under the suite's independently owned case directory. -/
def clone (ctx : Context) (source : FilePath) (name : String) : IO FilePath := do
  let target := ctx.temporary / "base-diff" / name
  copyRegistry ctx source target
  pure target

/-- Exercise one exact ordinary or explicitly permitted legacy supersession transition. -/
def check (ctx : Context) (label : String) (positive : Bool) (before after : FilePath)
    (diagnostic : String := "") (supersession : Bool := false) : IO Unit := do
  let options := if supersession then #["--allow-supersession"] else #[]
  discard <| expect ctx label positive (ctx.command "base-diff"
    (options ++ #["--fixture-dirs",before.toString,after.toString])) diagnostic

/-- Validate each original positive registry snapshot independently of the transition checker. -/
def registry (ctx : Context) (label : String) (root : FilePath) : IO Unit := do
  discard <| expect ctx label true (ctx.gate "registry" root)

/-- Check exact preservation, append-only historical correction events, page identity and phase monotonicity. -/
def basicCases (ctx : Context) (production : FilePath) : IO FilePath := do
  let base ← clone ctx production "base"
  mutateLine base "claims.tsv" 2 #[(8,"1111111111111111111111111111111111111111")]
  let good ← clone ctx base "good"
  registry ctx "base-snapshot-registry" base
  registry ctx "good-snapshot-registry" good
  check ctx "base-good" true base good
  let fake ← clone ctx base "historical-fake-edge"
  add fake "claim-successors.tsv" "SE-TASAKI2020-9999\tCORPUS-NORMALIZATION-TASAKI2020-2026\tCC-TASAKI2020-0001\tCL-TASAKI2020-0287\t99\texisting_duplicate\tCL-TASAKI2020-0001"
  check ctx "historical-fake-edge" false base fake "correction ledger"
  let deleted ← clone ctx base "deletion"
  rewrite deleted "pages.tsv" fun index row => if index == 2 then none else some row
  check ctx "base-deletion" false base deleted
  let drift ← clone ctx base "drift"
  rewrite drift "pages.tsv" fun index row => some (if index == 2 then row.set! 5 (row[5]! ++ "-drift") else row)
  check ctx "base-drift" false base drift
  let regression ← clone ctx base "regression"
  replace regression "phase.tsv" #["phase","census"]
  check ctx "base-regression" false base regression
  pure base

/-- Preserve the complete legacy source-reference input when copying a supersession counterfactual. -/
def copyReference (source target : FilePath) : IO Unit := do
  write target "references/tasaki-2020.tsv" (← IO.FS.readFile (source / "references/tasaki-2020.tsv"))

/-- Check reviewed legacy supersession against the actual last claim and its computed next source order. -/
def supersessionCases (ctx : Context) (production : FilePath) : IO Unit := do
  let base ← clone ctx production "supersession-base"
  for name in #["tracks.tsv","sources.tsv","source-invariants.tsv","source-progress.tsv","source-items.tsv","item-claims.tsv"] do
    IO.FS.removeFile (base / "registry" / name)
  write base "references/tasaki-2020.tsv" "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes\nTASAKI2020\truntime.pdf\t2020.ed1\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tfrozen\truntime\n"
  replace base "phase.tsv" #["phase","census"]
  headerOnly base "claim-vocabulary-review.tsv"
  let good ← clone ctx base "supersession-good"
  copyReference base good
  let claims ← table good "claims.tsv"
  let old := claims.back!
  let newId := "CL-TASAKI2020-9999"
  let parts := old[2]!.splitOn "."
  ensure (parts.length >= 2) "legacy last claim has no source-order component"
  let number := toString (parts[1]!.toNat! + 1)
  let nextOrder := parts[0]! ++ "." ++ String.ofList (List.replicate (4 - number.length) '0') ++ number
  writeTable good "claims.tsv" <| claims.set! (claims.size - 1)
    (setFields old #[(11,"true"),(12,newId),(13,"runtime-supersession"),(14,"RUNTIME-REVIEW")])
  append good "claims.tsv" #[#[newId,old[1]!,nextOrder,old[3]!,"runtime successor","assertion","lemma",
    "Runtime successor claim.","PENDING","NONE","NONE","false","NONE","NONE","NONE"]]
  let bad ← clone ctx good "supersession-bad"
  copyReference good bad
  mutate bad "claims.tsv" old[0]! 13 "NONE"
  registry ctx "supersession-snapshot-registry" good
  check ctx "supersession-default-reject" false base good
  check ctx "supersession-dedicated-accept" true base good "" true
  check ctx "supersession-dedicated-reject" false base bad "" true

/-- Check staged claim OID finalization independently from immutable already-fixed content identities. -/
def claimOidCases (ctx : Context) (production frozenBase : FilePath) : IO Unit := do
  let base ← clone ctx production "claim-oid-base"
  let good ← clone ctx base "claim-oid-good"
  mutateLine good "claims.tsv" 2 #[(8,"1111111111111111111111111111111111111111")]
  let bad ← clone ctx base "claim-oid-bad"
  mutateLine bad "claims.tsv" 2 #[(8,"invalid")]
  let changed ← clone ctx frozenBase "claim-oid-freeze-bad"
  mutateLine changed "claims.tsv" 2 #[(8,"2222222222222222222222222222222222222222")]
  registry ctx "claim-oid-base-snapshot-registry" base
  registry ctx "claim-oid-good-snapshot-registry" good
  check ctx "claim-oid-transition" true base good
  check ctx "claim-oid-invalid" false base bad
  check ctx "claim-oid-frozen" false frozenBase changed

/-- Check complete source fingerprints, stable editions, matched OID widths and coverage monotonicity. -/
def lifecycleCases (ctx : Context) (production frozenBase : FilePath) : IO Unit := do
  let base ← clone ctx production "lifecycle-base"
  let good ← clone ctx base "lifecycle-good"
  registry ctx "lifecycle-base-snapshot-registry" base
  registry ctx "lifecycle-good-snapshot-registry" good
  check ctx "reference-lifecycle" true base good
  for (label,name,source,col,value) in #[
      ("reference-partial-oid","lifecycle-partial-oid",base,14,""),
      ("reference-bad-edition","lifecycle-bad-edition",base,8,"changed.edition"),
      ("reference-pending-edition","registry-post-edition-pending",base,8,"pending"),
      ("reference-mixed-oid-width","registry-source-mixed-width",base,15,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"),
      ("reference-coverage-regress","lifecycle-regress",frozenBase,16,"pass2"),
      ("reference-edition-frozen","lifecycle-edition-drift",good,8,"other.edition"),
      ("reference-oid-frozen","lifecycle-oid-drift",good,14,"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")] do
    let target ← clone ctx source name
    mutateLine target "sources.tsv" 2 #[(col,value)]
    check ctx label false source target

/-- Check independently frozen vocabulary type and declaration values with separate registry snapshots. -/
def vocabularyCases (ctx : Context) (production : FilePath) : IO Unit := do
  let base ← clone ctx production "vocabulary-base"
  let good ← clone ctx base "vocabulary-good"
  let changedType ← clone ctx good "vocabulary-type-regression"
  mutateLine changedType "vocabulary.tsv" 2 #[(6,"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
  let changedValue ← clone ctx good "vocabulary-regression"
  mutateLine changedValue "vocabulary.tsv" 2 #[(7,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")]
  registry ctx "vocabulary-base-snapshot-registry" base
  registry ctx "vocabulary-good-snapshot-registry" good
  registry ctx "vocabulary-type-regression-snapshot-registry" changedType
  check ctx "vocabulary-type-freeze" true base good
  check ctx "vocabulary-type-only-drift" false good changedType "vocabulary type OID regressed"
  check ctx "vocabulary-declaration-only-drift" false good changedValue "vocabulary declaration OID regressed"
  let migration ← clone ctx production "review-token-migration-base"
  rewrite migration "claim-vocabulary-review.tsv" fun _ row =>
    some (if row[2]?.getD "" == "VOCABULARY-INDEPENDENT-REVIEW" then row.set! 2 "R3-INDEPENDENT-REVIEW-P0" else row)
  rewrite migration "source-progress.tsv" fun index row => some (if index > 1 then row.set! 2 "R3-INDEPENDENT-REVIEW-P0" else row)
  check ctx "review-token-migration-positive" true migration production
  let arbitrary ← clone ctx production "review-ref-arbitrary"
  mutateLine arbitrary "claim-vocabulary-review.tsv" 2 #[(2,"ARBITRARY-REVIEW-REF")]
  check ctx "review-ref-arbitrary-reject" false production arbitrary "vocabulary review"
/-- Check that semantic proof values may change without reopening a hole and provenance remains independently mutable. -/
def proofCases (ctx : Context) (production : FilePath) : IO Unit := do
  let base ← clone ctx production "proof-value-base"
  replace base "bindings.tsv" #[bindingHeader,bindingRow]
  let rewritten ← clone ctx base "proof-value-rewritten"
  mutateLine rewritten "bindings.tsv" 2 #[(11,"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee")]
  let reopened ← clone ctx base "proof-value-reopened"
  mutateLine reopened "bindings.tsv" 2 #[(11,"NONE")]
  let review ← clone ctx base "binding-review-ref-updated"
  mutateLine review "bindings.tsv" 2 #[(14,"RUNTIME-REVIEW-UPDATED")]
  check ctx "proof-value-rewritten" true base rewritten
  check ctx "proof-value-reopened" false base reopened "proof value regressed to an unresolved hole"
  check ctx "binding-review-provenance-updated" true base review

/-- Freeze axiom identities and accept only empty historical infrastructure schema migrations. -/
def schemaCases (ctx : Context) (production frozenBase : FilePath) : IO Unit := do
  let base ← clone ctx production "axiom-fixed-base"
  replace base "axioms.tsv" #[axiomHeader,axiomRow]
  let stable ← clone ctx base "axiom-fixed-stable"
  let changed ← clone ctx base "axiom-type-changed"
  mutateLine changed "axioms.tsv" 2 #[(7,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")]
  let reopened ← clone ctx base "axiom-type-reopened"
  mutateLine reopened "axioms.tsv" 2 #[(7,"PENDING")]
  let pending ← clone ctx base "axiom-pending-base"
  mutateLine pending "axioms.tsv" 2 #[(7,"PENDING")]
  let fixed ← clone ctx base "axiom-pending-fixed"
  let empty ← clone ctx production "old-empty-schemas"
  replace empty "bindings.tsv" #[oldBindingHeader]
  replace empty "axioms.tsv" #[oldAxiomHeader]
  let oldBinding ← clone ctx production "old-populated-bindings"
  replace oldBinding "bindings.tsv" #[oldBindingHeader,
    "CL-TASAKI2020-0001\tLatticeSystem.Claims.Front.statement0001\tLatticeSystem.Claims.Front.claim0001\tLatticeSystem.Claims.Front\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tNONE"]
  let currentBinding ← clone ctx production "current-populated-bindings"
  replace currentBinding "bindings.tsv" #[bindingHeader,bindingRow]
  let oldAxiom ← clone ctx base "old-populated-axioms"
  rewrite oldAxiom "axioms.tsv" fun _ row => some (row.extract 0 7)
  check ctx "axiom-type-fixed-stable" true base stable
  check ctx "axiom-type-pending-fixed" true pending fixed
  check ctx "axiom-type-changed" false base changed "axiom type OID regressed"
  check ctx "axiom-type-reopened" false base reopened "axiom type OID regressed"
  check ctx "old-populated-bindings" false oldBinding currentBinding "base bindings.tsv carries rows under an unsupported schema"
  check ctx "old-populated-axioms" false oldAxiom base "base axioms.tsv carries rows under an unsupported schema"
  check ctx "old-empty-schemas-migrate" true empty frozenBase

/-- Run every ordinary transition and all ten independent positive registry snapshots. -/
def run (ctx : Context) : IO Unit := do
  let passed ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let production := ctx.temporary / "production"
  copyRegistry ctx ctx.project production
  IO.FS.createDirAll (ctx.temporary / "base-diff")
  let baseline ← fingerprint ctx production
  let frozenBase ← basicCases ctx production
  supersessionCases ctx production
  claimOidCases ctx production frozenBase
  lifecycleCases ctx production frozenBase
  vocabularyCases ctx production
  proofCases ctx production
  schemaCases ctx production frozenBase
  discard <| expect ctx "invalid-base-ref" false
    (ctx.command "base-diff" #[ctx.project.toString,"refs/heads/runtime-base-ref-that-does-not-exist"])
  ensure ((← fingerprint ctx production) == baseline) "immutable production baseline changed"
  ensure ((← ctx.accepted.get) - passed == 21 && (← ctx.rejected.get) - rejected == 24)
    "base-diff matrix differs from 45 cases (21 positive, 24 negative)"
  IO.println "test-base-diff-runtime: ok (45 cases; 21 positive, 24 negative)"

end Checker.Tests.BaseDiff
