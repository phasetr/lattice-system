import Checker.Publication.Items

/-! Explicit public projections exclude source text, local references, hashes and review-private fields. -/
namespace Checker.Publication
open Lean System Checker.CheckAll

/-- Group an ordered relation without sorting or deduplicating away provenance multiplicity. -/
def relationIndex (rows : Array Row) (owner value : String) : IO (Std.HashMap String (Array String)) :=
  rows.foldlM (fun result row => do
    let id ← str row owner
    pure (result.insert id ((result[id]?.getD #[]).push (← str row value)))) {}

/-- Count a public status predicate without changing row or dictionary iteration semantics. -/
def countRows (rows : Array Row) (predicate : Row → IO Bool) : IO Nat :=
  rows.foldlM (fun count row => do pure (if ← predicate row then count+1 else count)) 0

/-- Construct the reviewed public catalog with conservative lifecycle, binding and proof statuses. -/
def publicCatalog (data : Data) : IO Json := do
  validateItems data
  let phaseRows ← data.rows "phase"
  require (phaseRows.size == 1) "phase registry must contain exactly one value"
  let phase ← str phaseRows[0]! "phase"
  let claimRows ← data.rows "claims"; let vocabularyRows ← data.rows "vocabulary"
  let reviewRows ← data.rows "claim_vocabulary_review"; let progressRows ← data.rows "source_progress"
  let claims ← indexUnique claimRows "claim_id" "claim"
  let vocabulary ← indexUnique vocabularyRows "vocabulary_id" "vocabulary"
  let reviews ← indexUnique reviewRows "claim_id" "vocabulary review"
  let progress ← indexUnique progressRows "source_id" "source progress"
  let bindings ← indexUnique (← data.rows "bindings") "claim_id" "binding"
  let axioms ← indexUnique (← data.rows "axioms") "axiom_id" "axiom"
  let vocabularyLinks ← data.rows "claim_vocabulary"
  let vocabularyByClaim ← relationIndex vocabularyLinks "claim_id" "vocabulary_id"
  let axiomsByClaim ← relationIndex (← data.rows "claim_axioms") "claim_id" "axiom_id"
  let claimsByItem ← (← data.rows "item_claims").foldlM (fun claimsByItem relation => do
    let id ← str relation "item_id"
    pure (claimsByItem.insert id ((claimsByItem[id]?.getD #[]).push
      (← integer (← str relation "position"),← str relation "claim_id"))))
    ({} : Std.HashMap String (Array (Int × String)))
  let publicItems ← (← data.rows "source_items").mapM fun item => do
    let itemId ← str item "item_id"
    let publicClaims ← ((claimsByItem[itemId]?.getD #[]).qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))).mapM fun (_,claimId) => do
      let claim ← lookup claims claimId
      let binding := bindings[claimId]?
      let axiomIds := axiomsByClaim[claimId]?.getD #[]
      let requiredVocabulary ← (vocabularyByClaim[claimId]?.getD #[]).mapM fun id => do
        pure (Json.mkObj [("vocabulary_id",toJson id),("declaration",← field (← lookup vocabulary id) "declaration")])
      let lifecycle ← if (← field claim "tombstone") == toJson "true" then
        pure (if (← field claim "superseded_by") != toJson "NONE" then "superseded" else "tombstoned")
        else pure "active"
      let reviewed := reviews.contains claimId
      let ready ← if reviewed then do
        let sourceProgress ← lookup progress (← str claim "source_id")
        pure (#["vocabulary_reviewed","skeleton_frozen","proof_active","complete"].contains (← str sourceProgress "lifecycle"))
        else pure false
      let bindingField := fun name => do
        match binding with | some row => field row name | none => pure (toJson "NONE")
      let proofRecorded ← match binding with
        | some row => pure ((← field row "proof_decl") != toJson "NONE")
        | none => pure false
      let registeredAxioms ← axiomIds.mapM fun id => do
        let row ← lookup axioms id
        pure (Json.mkObj [("axiom_id",toJson id),("declaration",← field row "declaration"),("category",← field row "category")])
      let basis ← match reviews[claimId]? with
        | some row => field row "basis"
        | none => pure (toJson "not_reviewed")
      pure <| Json.mkObj [
        ("claim_id",toJson claimId),("disposition",← field claim "disposition"),("subkind",← field claim "subkind"),
        ("lifecycle",toJson lifecycle),("successor_claim",← field claim "superseded_by"),
        ("vocabulary_status",toJson (if ready then "vocabulary_ready" else if reviewed then "review_staged" else "not_reviewed")),
        ("binding_status",toJson (if binding.isSome then "bound" else "not_bound")),
        ("statement_declaration",← bindingField "statement_decl"),("statement_module",← bindingField "module"),
        ("proof_status",toJson (if proofRecorded then "proof_declaration_registered" else "not_recorded")),
        ("proof_declaration",← bindingField "proof_decl"),
        ("axiom_status",toJson (if axiomIds.isEmpty then "not_assessed" else "registered_dependencies")),
        ("registered_axioms",toJson registeredAxioms),("vocabulary_basis",basis),
        ("required_vocabulary",toJson requiredVocabulary)]
    let publicItem ← project item #["item_id","source_id","order_key","page_id","item_kind",
      "source_label","title","locator","public_group","public_slug"]
    pure (publicItem.setObjVal! "claims" (toJson publicClaims))
  let sourceRows ← data.rows "sources"
  let sourcesById ← indexUnique sourceRows "source_id" "source"
  let (groups,_) ← publicItems.foldlM (fun (groups,groupIndex) item => do
    let source ← str item "source_id"; let slug ← str item "public_slug"; let title ← str item "public_group"
    let key := (source,slug)
    if let some index := groupIndex[key]? then
      let current := groups[index]!
      require ((← str current "public_group") == title) ("public group slug collision: " ++ slug)
      let ids ← arr current "item_ids"
      pure (groups.set! index (current.setObjVal! "item_ids" (toJson (ids.push (← field item "item_id")))),groupIndex)
    else
      let group := Json.mkObj [("source_id",toJson source),
        ("source_public_slug",← field (← lookup sourcesById source) "public_slug"),
        ("public_group",toJson title),("public_slug",toJson slug),("item_ids",toJson #[← field item "item_id"])]
      let groupIndex := groupIndex.insert key groups.size
      pure (groups.push group,groupIndex))
    ((#[],{}) : Array Json × Std.HashMap (String × String) Nat)
  let tracks ← (← data.rows "tracks").mapM (project · #["track_id","position","title","public_slug"])
  let sources ← sourceRows.mapM fun row => do
    let publicSource ← project row #["source_id","track_id","source_position","source_kind","citation_key",
      "title","authors","year","edition","identifier_kind","identifier","public_url","public_slug","coverage"]
    let lifecycle ← field (← lookup progress (← str row "source_id")) "lifecycle"
    pure (publicSource.setObjVal! "lifecycle" lifecycle)
  let active ← countRows claimRows (fun row => do pure ((← field row "tombstone") == toJson "false"))
  let targets ← countRows claimRows (fun row => do pure ((← field row "tombstone") == toJson "false" && (← field row "disposition") != toJson "out_of_scope"))
  let tombstoned ← countRows claimRows (fun row => do pure ((← field row "tombstone") == toJson "true"))
  let mathlibOnly ← countRows reviewRows (fun row => do pure ((← field row "basis") == toJson "mathlib_only"))
  let projectVocabulary ← countRows reviewRows (fun row => do pure ((← field row "basis") == toJson "project_vocabulary"))
  let publicVocabulary ← vocabularyRows.mapM (project · #["vocabulary_id","declaration","module","declaration_kind","origin","design_role","finiteness_scope"])
  return Json.mkObj [("schema_version",toJson (2 : Nat)),("phase",toJson phase),
    ("summary",Json.mkObj [("active_claims",toJson active),("formalization_target_claims",toJson targets),
      ("tombstoned_claims",toJson tombstoned),("source_items",toJson publicItems.size),
      ("mathlib_only_claims",toJson mathlibOnly),("project_vocabulary_claims",toJson projectVocabulary),
      ("vocabulary_declarations",toJson publicVocabulary.size),("claim_vocabulary_links",toJson vocabularyLinks.size)]),
    ("status_semantics",Json.mkObj [
      ("vocabulary_status",toJson "vocabulary_ready requires both a review row and a vocabulary-reviewed-or-later source lifecycle; review_staged is not ready"),
      ("binding_status",toJson "not_bound means no binding row is registered"),
      ("proof_status",toJson "not_recorded does not assert that a proof is absent from the source"),
      ("axiom_status",toJson "not_assessed is not an axiom-free claim")]),
    ("tracks",toJson tracks),("sources",toJson sources),("vocabulary",toJson publicVocabulary),
    ("groups",toJson groups),("items",toJson publicItems)]

end Checker.Publication
