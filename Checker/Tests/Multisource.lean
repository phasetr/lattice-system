import Checker.Tests.Fixtures

/-! Multi-source census, lifecycle, ordering and immutable transition regressions. -/
namespace Checker.Tests.Multisource
open System Checker.TestSupport Checker.Tests.Fixtures

/-- Construct the original two-source corpus with independent canonical census identities. -/
def base (ctx : Context) : IO FilePath := do
  let root := ctx.temporary / "base"
  newTarget ctx root
  replace root "slices.tsv" #["slice_id\tposition\tclaim_id"]
  replace root "dependencies.tsv" #["claim_id\trole\ttarget_claim_id\trationale"]
  replace root "bindings.tsv" #["claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref"]
  replace root "claim-context.tsv" #["claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref"]
  replace root "statement-modules.tsv" #["module\tsource_path\trole"]
  replace root "statement-imports.tsv" #["module\tposition\timported_module\tis_exported\tis_meta\timport_all"]
  replace root "axioms.tsv" #["axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid"]
  replace root "claim-axioms.tsv" #["claim_id\taxiom_id"]
  replace root "claim-vocabulary-review.tsv" #["claim_id\tbasis\treview_ref"]
  replace root "vocabulary.tsv" #["vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope"]
  replace root "claim-vocabulary.tsv" #["claim_id\tvocabulary_id"]
  replace root "modules.tsv" #["module\tsource_path\trole"]
  replace root "imports.tsv" #["module\tposition\timported_module\tis_exported\tis_meta\timport_all"]
  replace root "correction-events.tsv" #["event_id\tevent_position\tsource_id\tbase_commit\treview_ref"]
  replace root "claim-normalization-reviews.tsv" #["review_id\tevent_id\treview_position\tclaim_id\treview_scope\toutcome\tstatus\trationale\treview_ref"]
  replace root "claim-corrections.tsv" #["correction_id\tevent_id\tcorrection_position\treview_id\tclaim_id\taction\told_disposition\told_subkind\tnew_disposition\tnew_subkind"]
  replace root "claim-successors.tsv" #["successor_edge_id\tevent_id\tcorrection_id\tpredecessor_claim_id\tsuccessor_position\trelation\tsuccessor_claim_id"]
  replace root "source-item-additions.tsv" #["item_addition_id\tevent_id\tcorrection_id\taddition_position\titem_id\treview_ref"]
  replace root "claim-content-amendments.tsv" #["amendment_id\tevent_id\tcorrection_id\tclaim_id\told_content_oid\tnew_content_oid\tpage_source_oid\treview_ref"]
  replace root "claim-location-amendments.tsv" #["location_amendment_id\tevent_id\tcorrection_id\tclaim_id\titem_id\told_claim_locator\tnew_claim_locator\told_item_locator\tnew_item_locator\treview_ref"]
  replace root "phase.tsv" #[
    "phase",
    "census",
  ]
  replace root "tracks.tsv" #[
    "track_id\tposition\ttitle\tpublic_slug",
    "TR-A\t1\tTrack A\ttrack-a",
    "TR-B\t2\tTrack B\ttrack-b",
  ]
  replace root "sources.tsv" #[
    "source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage",
    "SRA\tTR-A\t1\tpaper\tSRA\tSource A\tAuthor A\t2025\tv1\tnone\tNONE\tNONE\tsource-a\tSourceA\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\treconciled",
    "SRB\tTR-B\t1\tpaper\tSRB\tSource B\tAuthor B\t2026\tv1\tnone\tNONE\tNONE\tsource-b\tSourceB\tcccccccccccccccccccccccccccccccccccccccc\tdddddddddddddddddddddddddddddddddddddddd\treconciled",
  ]
  replace root "source-progress.tsv" #[
    "source_id\tlifecycle\treview_ref",
    "SRA\tcensus_reconciled\tREVIEW-A",
    "SRB\tcensus_reconciled\tREVIEW-B",
  ]
  replace root "pages.tsv" #[
    "page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid",
    "PG-SRA-0001\tSRA\t000001\t1\t1\t1\tcontent\tcomplete\tcomplete\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "PG-SRB-0001\tSRB\t000001\t1\t1\t1\tcontent\tcomplete\tcomplete\tcccccccccccccccccccccccccccccccccccccccc",
  ]
  replace root "claims.tsv" #[
    "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref",
    "CL-SRA-0001\tSRA\t000001.0001\tPG-SRA-0001\tPDF p. 1; paragraph 1\tassertion\tunnumbered_obligation\tClaim A\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE",
    "CL-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tPDF p. 1; paragraph 1\tassertion\tunnumbered_obligation\tClaim B\tcccccccccccccccccccccccccccccccccccccccc\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE",
  ]
  replace root "source-items.tsv" #[
    "item_id\tsource_id\torder_key\tpage_id\titem_kind\tsource_label\ttitle\tlocator\tpublic_group\tpublic_slug\treview_ref",
    "IT-SRA-0001\tSRA\t000001.0001\tPG-SRA-0001\tunlabeled\tNONE\tNONE\tPDF p. 1; paragraph 1\tChapter 01\tchapter-01\tREVIEW-A",
    "IT-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tunlabeled\tNONE\tNONE\tPDF p. 1; paragraph 1\tChapter 01\tchapter-01\tREVIEW-B",
  ]
  replace root "item-claims.tsv" #[
    "item_id\tposition\tclaim_id",
    "IT-SRA-0001\t1\tCL-SRA-0001",
    "IT-SRB-0001\t1\tCL-SRB-0001",
  ]
  let sources ← table root "sources.tsv"
  let pages ← table root "pages.tsv"
  let progress ← table root "source-progress.tsv"
  let header := #["source_id","physical_page_count","active_claim_count","formalization_target_count",
    "equation_pair_count","no_claim_page_count","census_oid","review_ref"]
  let invariants ← (sources.extract 1 sources.size).mapM fun source => do
    let id := source[0]!
    let some state := progress.find? (fun row => row[0]?.getD "" == id)
      | throw <| IO.userError ("fixture source has no progress record " ++ id)
    let count := (pages.filter fun row => row[1]?.getD "" == id).size
    pure #[id,toString count,"0","0","0","0","PENDING",state[2]!]
  writeTable root "source-invariants.tsv" (#[header] ++ invariants)
  refresh ctx root
  pure root

/-- Clone one independent mutation without altering the shared baseline. -/
def clone (ctx : Context) (source : FilePath) (name : String) : IO FilePath := do
  let target := ctx.temporary / name
  copyFixture ctx source target
  pure target

/-- Form the original explicit fixture-census route while keeping all other static gates direct. -/
def gateCommand (ctx : Context) (name : String) (root : FilePath) : Command :=
  if name == "census" then
    {ctx.gate name root with args := #["--gate",name,"--fixture",root.toString]}
  else ctx.gate name root

/-- Count one actual native gate invocation with the original status and diagnostic contract. -/
def gate (ctx : Context) (label name : String) (root : FilePath) (positive : Bool := true)
    (diagnostic : String := "") : IO Unit := do
  discard <| expect ctx label positive (gateCommand ctx name root) diagnostic

/-- Count one ordinary or legacy supersession base-diff invocation with exact fixture roots. -/
def diff (ctx : Context) (label : String) (before after : FilePath) (positive : Bool := true)
    (diagnostic : String := "") (supersession : Bool := false) : IO Unit := do
  let options := if supersession then #["--allow-supersession"] else #[]
  discard <| expect ctx label positive (ctx.command "base-diff"
    (options ++ #["--fixture-dirs",before.toString,after.toString])) diagnostic

/-- Keep every R4 artifact table header-only throughout the independent multi-source census path. -/
def censusArtifactCases (ctx : Context) (initial : FilePath) : IO Unit := do
  for (name,row) in #[
      ("bindings","CL-SRA-0001\tFixture.statement\tNONE\tFixture.Module\tdefinition\tdefinition_value\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tFIXTURE-REVIEW"),
      ("claim-context","CL-SRA-0002\t1\tCL-SRA-0001\tassumption\tsame_item\tFIXTURE-REVIEW"),
      ("statement-modules","LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf"),
      ("statement-imports","LatticeSystem.Claims.Front\t1\tMathlib\ttrue\tfalse\tfalse")] do
    let target ← clone ctx initial ("census-r4-" ++ name)
    add target (name ++ ".tsv") row
    gate ctx ("census-r4-" ++ name) "census" target false ("census capability requires header-only " ++ name ++ ".tsv")

/-- Check source-specific page identities, census counts, canonical positions and lifecycle limits. -/
def sourceCases (ctx : Context) (initial : FilePath) : IO Unit := do
  for (label,name,file,line,fields,validator,diagnostic) in #[
      ("unpadded-chapter","unpadded-chapter","source-items.tsv",2,#[(8,"Chapter 1"),(9,"chapter-1")],"source-items","numeric chapter group is not zero-padded"),
      ("id-source-mismatch","id-mismatch","pages.tsv",2,#[(0,"PG-SRB-0002")],"order","page ID/source mismatch"),
      ("per-source-count","count","source-invariants.tsv",2,#[(2,"2")],"census","claim census invariant failed for SRA"),
      ("per-source-order","order","sources.tsv",3,#[(2,"2")],"sources","source positions are not contiguous"),
      ("lifecycle-mismatch","lifecycle","source-progress.tsv",2,#[(1,"vocabulary_reviewed")],"lifecycle","source lifecycle exceeds checker capability SRA")] do
    let target ← clone ctx initial name
    mutateLine target file line fields
    gate ctx label validator target false diagnostic

/-- Check later sources may remain at earlier independent lifecycle stages without weakening prior acceptance. -/
def mixedLifecycleCases (ctx : Context) (initial : FilePath) : IO Unit := do
  let mixed ← clone ctx initial "mixed-census"
  replace mixed "phase.tsv" #["phase","vocabulary"]
  mutateLine mixed "sources.tsv" 2 #[(16,"frozen")]
  mutateLine mixed "source-progress.tsv" 2 #[(1,"vocabulary_reviewed")]
  replace mixed "claim-vocabulary-review.tsv" #["claim_id\tbasis\treview_ref","CL-SRA-0001\tmathlib_only\tREVIEW-A"]
  gate ctx "mixed-census-registry" "registry" mixed
  gate ctx "mixed-census-census" "census" mixed
  let registered ← clone ctx mixed "mixed-registered"
  mutateLine registered "sources.tsv" 3 #[(14,""),(15,""),(16,"pending")]
  mutateLine registered "source-progress.tsv" 3 #[(1,"registered")]
  rewrite registered "source-invariants.tsv" fun line row => if line == 3 then none else some row
  for name in #["pages.tsv","claims.tsv","source-items.tsv"] do
    rewrite registered name fun line row => if line == 1 || row[1]! != "SRB" then some row else none
  rewrite registered "item-claims.tsv" fun line row => if line == 1 || row[0]! != "IT-SRB-0001" then some row else none
  gate ctx "mixed-registered-registry" "registry" registered
  gate ctx "mixed-registered-census" "census" registered
  gate ctx "mixed-registered-source-items" "source-items" registered

/-- Distinguish valid global dependency order from reversed edges and missing independent review rationales. -/
def dependencyCases (ctx : Context) (initial : FilePath) : IO Unit := do
  let good ← clone ctx initial "dependency-good"
  add good "dependencies.tsv" "CL-SRB-0001\trequires\tCL-SRA-0001\tCROSS-TRACK-REVIEW"
  gate ctx "dependency-good-order" "order" good
  for (label,name,row,diagnostic) in #[
      ("required-by-rationale","dependency-required-by","CL-SRB-0001\trequired_by\tCL-SRA-0001\tNONE","required_by needs review rationale"),
      ("cross-track-rationale","dependency-cross-track-rationale","CL-SRB-0001\trequires\tCL-SRA-0001\tNONE","cross-track dependency needs review rationale"),
      ("cross-source-dependency","dependency","CL-SRA-0001\trequires\tCL-SRB-0001\tCROSS-SOURCE-NEGATIVE","dependency target is not earlier in global source order")] do
    let target ← clone ctx initial name
    add target "dependencies.tsv" row
    gate ctx label "order" target false diagnostic
/-- Add the compact frozen through-vocabulary anti-regression records without claiming census-phase acceptance. -/
def diffBase (ctx : Context) (initial : FilePath) : IO FilePath := do
  let root ← clone ctx initial "diff-base"
  add root "slices.tsv" "SL-SRA-0001\t1\tCL-SRA-0001"
  add root "bindings.tsv" "CL-SRA-0001\tFixture.statement\tFixture.proof\tFixture.Module\tdefinition\tproof_proposition\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tproof_stub\ttheorem\tcccccccccccccccccccccccccccccccccccccccc\tNONE\tFixture.nonvacuity\tdddddddddddddddddddddddddddddddddddddddd\tMULTISOURCE-FIXTURE-REVIEW"
  add root "vocabulary.tsv" "VO-LS-0001\tFixture.term\tFixture.Module\tdefinition\tprimary\tNONE\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tgraph_core\tnone"
  pure root

/-- Freeze vocabulary, slices, capability, page state and claim object identities across unrelated sources. -/
def diffCorpusCases (ctx : Context) (initial good : FilePath) : IO Unit := do
  for (label,name,file,column,value,diagnostic) in #[
      ("base-vocabulary-type","diff-vocabulary-type","vocabulary.tsv",6,"cccccccccccccccccccccccccccccccccccccccc","vocabulary type OID regressed"),
      ("base-vocabulary-declaration","diff-vocabulary-declaration","vocabulary.tsv",7,"cccccccccccccccccccccccccccccccccccccccc","vocabulary declaration OID regressed"),
      ("base-slice-position","diff-slice-position","slices.tsv",1,"2","slice position changed"),
      ("base-page-pass","diff-page-pass","pages.tsv",7,"pending","page OID or census pass regressed"),
      ("base-page-oid","diff-page-oid","pages.tsv",9,"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee","page OID or census pass regressed"),
      ("base-claim-oid","diff-claim-oid","claims.tsv",8,"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee","claim OID or tombstone regressed")] do
    let target ← clone ctx initial name
    mutateLine target file 2 #[(column,value)]
    diff ctx label initial target false diagnostic
  let deleted ← clone ctx initial "diff-slice-deletion"
  headerOnly deleted "slices.tsv"
  diff ctx "base-slice-deletion" initial deleted false "slice membership disappeared"
  let phase ← clone ctx initial "diff-phase-base"
  mutateLine phase "phase.tsv" 2 #[(0,"vocabulary")]
  diff ctx "base-phase" phase good false "phase regression: vocabulary -> census"
  for name in #["claim-context","statement-modules","statement-imports"] do
    let target ← clone ctx initial ("diff-missing-" ++ name)
    IO.FS.removeFile (target / "registry" / (name ++ ".tsv"))
    diff ctx ("base-missing-" ++ name) initial target false ("current missing registry/" ++ name ++ ".tsv")

/-- Independently freeze every recorded R4 module, import and context relation despite another earlier-stage source. -/
def diffR4Cases (ctx : Context) (initial : FilePath) : IO Unit := do
  for (name,row,column,replacement,diagnostic) in #[
      ("statement-modules","LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf",2,"umbrella","statement source path/role changed"),
      ("statement-imports","LatticeSystem.Claims.Front\t1\tMathlib\ttrue\tfalse\tfalse",3,"false","statement-import disappeared or drifted"),
      ("claim-context","CL-SRA-0002\t1\tCL-SRA-0001\tassumption\tinherited\tFIXTURE-REVIEW",3,"term_reference","claim-context disappeared or drifted")] do
    let before ← clone ctx initial ("r4-frozen-" ++ name ++ "-base")
    add before (name ++ ".tsv") row
    diff ctx ("r4-frozen-" ++ name ++ "-stable") before before
    let after ← clone ctx before ("r4-frozen-" ++ name ++ "-current")
    mutateLine after (name ++ ".tsv") 2 #[(column,replacement)]
    diff ctx ("base-frozen-" ++ name) before after false diagnostic

/-- Freeze each semantic binding field individually while retaining the independently rewritable proof value. -/
def diffBindingCases (ctx : Context) (initial good : FilePath) : IO Unit := do
  let missing ← clone ctx initial "diff-binding"
  headerOnly missing "bindings.tsv"
  diff ctx "base-binding" initial missing false "binding disappeared or identity drifted"
  for column in #[2,3,4,5,6,7,8,9,10,11,13,14] do
    let target ← clone ctx initial ("diff-binding-column-" ++ toString column)
    mutateLine target "bindings.tsv" 2 #[(column - 1,"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee")]
    diff ctx ("base-binding-column-" ++ toString column) initial target false "binding disappeared or identity drifted"
  let proofValue ← clone ctx initial "diff-binding-proof-value"
  mutateLine proofValue "bindings.tsv" 2 #[(11,"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee")]
  diff ctx "binding-proof-value-rewritten" initial proofValue
  let tombstone ← clone ctx initial "diff-tombstone-base"
  mutateLine tombstone "claims.tsv" 2 #[(11,"true"),(12,"CL-SRB-0001"),(13,"RETIRED"),(14,"REVIEW")]
  diff ctx "base-tombstone-reversal" tombstone good false "claim OID or tombstone regressed" true
  let supersession ← clone ctx initial "diff-supersession"
  mutateLine supersession "claims.tsv" 2 #[(11,"true"),(12,"CL-SRB-0001"),(13,"RETIRED"),(14,"REVIEW")]
  diff ctx "base-supersession" initial supersession false "invalid dedicated supersession transition" true

/-- Run every multi-source structural and transition case using source-specific derived census metadata. -/
def run (ctx : Context) : IO Unit := do
  let passed ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let initial ← base ctx
  let baseline ← fingerprint ctx initial
  gate ctx "base-registry" "registry" initial
  gate ctx "base-census" "census" initial
  gate ctx "base-source-items" "source-items" initial
  censusArtifactCases ctx initial
  sourceCases ctx initial
  mixedLifecycleCases ctx initial
  dependencyCases ctx initial
  let frozen ← diffBase ctx initial
  let good ← clone ctx frozen "diff-good"
  diff ctx "diff-good" frozen good
  diffCorpusCases ctx frozen good
  diffR4Cases ctx frozen
  diffBindingCases ctx frozen good
  ensure ((← fingerprint ctx initial) == baseline) "multi-source baseline was mutated"
  ensure ((← ctx.accepted.get) - passed == 14 && (← ctx.rejected.get) - rejected == 41)
    "multisource matrix differs from 55 cases (14 positive, 41 negative)"
  IO.println "test-multisource: ok (55 cases; 14 positive, 41 negative)"

end Checker.Tests.Multisource
