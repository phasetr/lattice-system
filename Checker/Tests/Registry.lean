import Checker.Tests.Fixtures

/-! Production-derived and historical schema, census and lifecycle counterfactuals. -/
namespace Checker.Tests.Registry
open System Checker.TestSupport Checker.Tests.Fixtures

/-- A fixture starts from current corpus bytes and explicitly replaces only historical tables. -/
def legacy (ctx : Context) (production target : FilePath) : IO Unit := do
  copyRegistry ctx production target
  IO.FS.removeFile (target / "registry/sources.tsv")
  write target "references/tasaki-2020.tsv" "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes\nTASAKI2020\tfixture.pdf\t2020.ed1\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tpass1\tfixture\n"
  write target "registry/phase.tsv" "phase\ncensus\n"
  write target "registry/pages.tsv" "page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid\nPG-TASAKI2020-0001\tTASAKI2020\t000001\tNONE\t1\t1\tcontent\tcomplete\tpending\tPENDING\n"
  write target "registry/claims.tsv" "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref\nCL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tpage 1\tassertion\ttheorem\tFixture theorem.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n"
  write target "registry/slices.tsv" "slice_id\tposition\tclaim_id\nSL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001\n"
  write target "registry/dependencies.tsv" "claim_id\trole\ttarget_claim_id\trationale\n"
  write target "registry/bindings.tsv" "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref\nCL-TASAKI2020-0001\tLatticeSystem.Claims.Front.statement0001\tLatticeSystem.Claims.Front.claim0001\tLatticeSystem.Claims.Front\tdefinition\tproof_proposition\t0000000000000000000000000000000000000000\t1111111111111111111111111111111111111111\tproof_stub\ttheorem\t2222222222222222222222222222222222222222\tNONE\tNONE\tNONE\tLEGACY-FIXTURE-REVIEW\n"
  write target "registry/claim-context.tsv" "claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref\n"
  write target "registry/statement-modules.tsv" "module\tsource_path\trole\nLatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf\nLatticeSystem.Skeleton\tLatticeSystem/Skeleton.lean\tumbrella\n"
  write target "registry/statement-imports.tsv" "module\tposition\timported_module\tis_exported\tis_meta\timport_all\nLatticeSystem.Claims.Front\t1\tMathlib\ttrue\tfalse\tfalse\nLatticeSystem.Skeleton\t1\tLatticeSystem.Claims.Front\ttrue\tfalse\tfalse\n"
  write target "registry/axioms.tsv" "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid\nAX-PROJECT-0001\tLatticeSystem.Axioms.AbstractCStar.interfaceAxiom\tLatticeSystem.Axioms.AbstractCStar\tabstract_cstar\tnot-applicable\tfixture-rationale\treopen-when-implemented\tPENDING\n"
  write target "registry/claim-axioms.tsv" "claim_id\taxiom_id\nCL-TASAKI2020-0001\tAX-PROJECT-0001\n"
  write target "registry/claim-vocabulary-review.tsv" "claim_id\tbasis\treview_ref\n"
  write target "registry/vocabulary.tsv" "vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope\n"
  write target "registry/claim-vocabulary.tsv" "claim_id\tvocabulary_id\n"
  write target "registry/modules.tsv" "module\tsource_path\trole\n"
  write target "registry/imports.tsv" "module\tposition\timported_module\tis_exported\tis_meta\timport_all\n"

/-- Three ordered source claims make dependency and supersession defects observable. -/
def three (ctx : Context) (good target : FilePath) : IO Unit := do
  copyFixture ctx good target
  write target "registry/claims.tsv" "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref\nCL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tpage-1-claim-1\tassertion\ttheorem\tFirst-fixture-claim.\t1111111111111111111111111111111111111111\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\nCL-TASAKI2020-0002\tTASAKI2020\t000001.0002\tPG-TASAKI2020-0001\tpage-1-claim-2\tassertion\tlemma\tSecond-fixture-claim.\t2222222222222222222222222222222222222222\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\nCL-TASAKI2020-0003\tTASAKI2020\t000001.0003\tPG-TASAKI2020-0001\tpage-1-claim-3\tassertion\tlemma\tThird-fixture-claim.\t3333333333333333333333333333333333333333\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n"
  write target "registry/slices.tsv" "slice_id\tposition\tclaim_id\nSL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001\nSL-TASAKI2020-0001\t2\tCL-TASAKI2020-0002\nSL-TASAKI2020-0001\t3\tCL-TASAKI2020-0003\n"

/-- A complete frozen two-page fixture distinguishes structural and census acceptance. -/
def census (ctx : Context) (good target : FilePath) : IO Unit := do
  copyFixture ctx good target
  replace target "phase.tsv" #["phase","census"]
  editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
    let mut row := original
    if index == 2 then
      row := row.set! 2 "2020.ed1"
      row := row.set! 3 "3333333333333333333333333333333333333333"
      row := row.set! 4 "4444444444444444444444444444444444444444"
      row := row.set! 5 "frozen"
    return if (true) then some row else none
  write target "registry/pages.tsv" "page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid\nPG-TASAKI2020-0001\tTASAKI2020\t000001\tNONE\t1\tNONE\tcontent\tcomplete\tcomplete\t4444444444444444444444444444444444444444\nPG-TASAKI2020-0002\tTASAKI2020\t000002\t1\t2\t1.1\tcontent\tcomplete\tcomplete\t4444444444444444444444444444444444444444\n"
  write target "registry/claims.tsv" "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref\nCL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tPDF p. 1; print p. NONE; NONE; equation (F.1)\tassertion\tequation\tFixture-equation.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\nCL-TASAKI2020-0002\tTASAKI2020\t000002.0001\tPG-TASAKI2020-0002\tPDF-p.2-section-1.1\tassertion\tunnumbered_obligation\tFixture-prose-claim.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n"
  for name in #["slices.tsv","dependencies.tsv","bindings.tsv","claim-context.tsv","axioms.tsv","claim-axioms.tsv","statement-modules.tsv","statement-imports.tsv"] do headerOnly target name

/-- Construct the registry-duplicate-id through registry-slice-duplicate counterfactuals. -/
def cases0 (ctx : Context) (good threeRoot : FilePath) : IO Unit := do
  -- registry-duplicate-id
  do
    let target := ctx.temporary / "registry-duplicate-id"
    copyFixture ctx good target
    add target "claims.tsv" "CL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tduplicate\tassertion\ttheorem\tDuplicate.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE"
  -- registry-bad-fk
  do
    let target := ctx.temporary / "registry-bad-fk"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 3 "PG-TASAKI2020-9999"
      return if (true) then some row else none
  -- registry-bad-enum
  do
    let target := ctx.temporary / "registry-bad-enum"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 6 "invalid"
      return if (true) then some row else none
  -- registry-bad-order
  do
    let target := ctx.temporary / "registry-bad-order"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 2 "bad"
      return if (true) then some row else none
  -- registry-bad-header
  do
    let target := ctx.temporary / "registry-bad-header"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 1 then
        row := ("wrong_header".splitOn "\t").toArray
      return if (true) then some row else none
  -- registry-bad-column
  do
    let target := ctx.temporary / "registry-bad-column"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.extract 0 9
      return if (true) then some row else none
  -- registry-control-char
  do
    let target := ctx.temporary / "registry-control-char"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 5 "bad\u000bcontrol"
      return if (true) then some row else none
  -- registry-bad-id
  do
    let target := ctx.temporary / "registry-bad-id"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 0 "bad-page-id"
      return if (true) then some row else none
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 3 "bad-page-id"
      return if (true) then some row else none
  -- registry-page-missing-coordinate
  do
    let target := ctx.temporary / "registry-page-missing-coordinate"
    copyFixture ctx good target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 3 ""
      return if (true) then some row else none
  -- registry-slice-duplicate
  do
    let target := ctx.temporary / "registry-slice-duplicate"
    copyFixture ctx threeRoot target
    editFile target "registry/slices.tsv" fun _ row => some row
    let path := target / "registry/slices.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "SL-TASAKI2020-0002\t1\tCL-TASAKI2020-0001\n")

/-- Construct the registry-slice-position through registry-fk-slice counterfactuals. -/
def cases1 (ctx : Context) (threeRoot : FilePath) : IO Unit := do
  -- registry-slice-position
  do
    let target := ctx.temporary / "registry-slice-position"
    copyFixture ctx threeRoot target
    editFile target "registry/slices.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 1 "2"
      return if (true) then some row else none
  -- registry-dep-bad-role
  do
    let target := ctx.temporary / "registry-dep-bad-role"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\tprerequisite\tCL-TASAKI2020-0001\tNONE\n")
  -- registry-dep-order
  do
    let target := ctx.temporary / "registry-dep-order"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0001\trequires\tCL-TASAKI2020-0002\tNONE\n")
  -- registry-dep-cycle
  do
    let target := ctx.temporary / "registry-dep-cycle"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\tfrontier-exception\n")
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0003\trequired_by\tCL-TASAKI2020-0002\tfrontier-exception\n")
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0003\trequires\tCL-TASAKI2020-0001\tNONE\n")
  -- registry-dep-self
  do
    let target := ctx.temporary / "registry-dep-self"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-0002\tNONE\n")
  -- registry-dep-duplicate
  do
    let target := ctx.temporary / "registry-dep-duplicate"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-0001\tNONE\n")
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-0001\tNONE\n")
  -- registry-dep-rationale
  do
    let target := ctx.temporary / "registry-dep-rationale"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\tNONE\n")
  -- registry-dep-whitespace
  do
    let target := ctx.temporary / "registry-dep-whitespace"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\t bad\n")
  -- registry-dep-whitespace-em
  do
    let target := ctx.temporary / "registry-dep-whitespace-em"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\t bad\n")
  -- registry-fk-slice
  do
    let target := ctx.temporary / "registry-fk-slice"
    copyFixture ctx threeRoot target
    editFile target "registry/slices.tsv" fun index original => Id.run do
      let mut row := original
      if index == 4 then
        row := row.set! 2 "CL-TASAKI2020-9999"
      return if (true) then some row else none

/-- Construct the registry-fk-dependency through registry-supersession-missing-review counterfactuals. -/
def cases2 (ctx : Context) (good threeRoot superRoot : FilePath) : IO Unit := do
  -- registry-fk-dependency
  do
    let target := ctx.temporary / "registry-fk-dependency"
    copyFixture ctx threeRoot target
    editFile target "registry/dependencies.tsv" fun _ row => some row
    let path := target / "registry/dependencies.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-9999\tNONE\n")
  -- registry-fk-binding
  do
    let target := ctx.temporary / "registry-fk-binding"
    copyFixture ctx good target
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 0 "CL-TASAKI2020-9999"
      return if (true) then some row else none
  -- registry-fk-claim-axiom-claim
  do
    let target := ctx.temporary / "registry-fk-claim-axiom-claim"
    copyFixture ctx good target
    editFile target "registry/claim-axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 0 "CL-TASAKI2020-9999"
      return if (true) then some row else none
  -- registry-fk-claim-axiom-axiom
  do
    let target := ctx.temporary / "registry-fk-claim-axiom-axiom"
    copyFixture ctx good target
    editFile target "registry/claim-axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 1 "AX-PROJECT-9999"
      return if (true) then some row else none
  -- registry-supersession-good
  do
    let target := ctx.temporary / "registry-supersession-good"
    copyFixture ctx superRoot target
  -- registry-supersession-self
  do
    let target := ctx.temporary / "registry-supersession-self"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 11 "true"
        row := row.set! 12 row[0]!
        row := row.set! 13 "bad-self"
        row := row.set! 14 "review-1"
      return if (true) then some row else none
  -- registry-supersession-cycle
  do
    let target := ctx.temporary / "registry-supersession-cycle"
    copyFixture ctx threeRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 11 "true"
        row := row.set! 12 "CL-TASAKI2020-0002"
        row := row.set! 13 "cycle-one"
        row := row.set! 14 "review-1"
      if index == 3 then
        row := row.set! 11 "true"
        row := row.set! 12 "CL-TASAKI2020-0001"
        row := row.set! 13 "cycle-two"
        row := row.set! 14 "review-2"
      return if (index < 4) then some row else none
  -- registry-supersession-incoherent
  do
    let target := ctx.temporary / "registry-supersession-incoherent"
    copyFixture ctx threeRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 12 "CL-TASAKI2020-0002"
      return if (true) then some row else none
  -- registry-supersession-missing-rationale
  do
    let target := ctx.temporary / "registry-supersession-missing-rationale"
    copyFixture ctx superRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 13 "NONE"
      return if (true) then some row else none
  -- registry-supersession-missing-review
  do
    let target := ctx.temporary / "registry-supersession-missing-review"
    copyFixture ctx superRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 14 "NONE"
      return if (true) then some row else none

/-- Construct the registry-exclusion-good through registry-axiom-categories-good counterfactuals. -/
def cases3 (ctx : Context) (good : FilePath) : IO Unit := do
  -- registry-exclusion-good
  do
    let target := ctx.temporary / "registry-exclusion-good"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 5 "out_of_scope"
        row := row.set! 9 "scope-reason"
        row := row.set! 10 "review-1"
      return if (true) then some row else none
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      return if (index == 1) then some row else none
  -- registry-binding-out-of-scope
  do
    let target := ctx.temporary / "registry-binding-out-of-scope"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 5 "out_of_scope"
        row := row.set! 9 "scope-reason"
        row := row.set! 10 "review-1"
      return if (true) then some row else none
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 2 "NONE"
        row := row.set! 5 "definition_value"
        row := row.set! 8 "definitional"
        row := row.set! 9 "NONE"
        row := row.set! 10 "NONE"
      return if (true) then some row else none
  -- registry-exclusion-missing-rationale
  do
    let target := ctx.temporary / "registry-exclusion-missing-rationale"
    copyFixture ctx (ctx.temporary / "registry-exclusion-good") target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 9 "NONE"
      return if (true) then some row else none
  -- registry-exclusion-missing-review
  do
    let target := ctx.temporary / "registry-exclusion-missing-review"
    copyFixture ctx (ctx.temporary / "registry-exclusion-good") target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 10 "NONE"
      return if (true) then some row else none
  -- registry-exclusion-incoherent
  do
    let target := ctx.temporary / "registry-exclusion-incoherent"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 9 "scope-reason"
        row := row.set! 10 "review-1"
      return if (true) then some row else none
  -- registry-remark-good
  do
    let target := ctx.temporary / "registry-remark-good"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 6 "remark"
      return if (true) then some row else none
  -- registry-bad-subkind
  do
    let target := ctx.temporary / "registry-bad-subkind"
    copyFixture ctx good target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 6 "editorial"
      return if (true) then some row else none
  -- registry-axiom-bad-category
  do
    let target := ctx.temporary / "registry-axiom-bad-category"
    copyFixture ctx good target
    editFile target "registry/axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 3 "analytic-limit"
      return if (true) then some row else none
  -- registry-axiom-bad-path
  do
    let target := ctx.temporary / "registry-axiom-bad-path"
    copyFixture ctx good target
    editFile target "registry/axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 1 "LatticeSystem.Axioms.State.bad"
        row := row.set! 2 "LatticeSystem.Axioms.State"
      return if (true) then some row else none
  -- registry-axiom-categories-good
  do
    let target := ctx.temporary / "registry-axiom-categories-good"
    copyFixture ctx good target
    for (name,category,index) in #[("State","state",2),("GNS","gns",3),("KMS","kms",4),("WeakDual","weak_dual",5),("Wigner","wigner",6),("ContentlessPredicate","contentless_predicate",7)] do
      let n := toString index
      let id := "AX-PROJECT-" ++ String.ofList (List.replicate (4-n.length) '0') ++ n
      add target "axioms.tsv" (String.intercalate "\t" [id,"LatticeSystem.Axioms." ++ name ++ ".fixture","LatticeSystem.Axioms." ++ name,category,"not-applicable","rationale","reopen","PENDING"])

/-- Construct the registry-source-missing through registry-skeleton-pending-axiom counterfactuals. -/
def cases4 (ctx : Context) (good : FilePath) : IO Unit := do
  -- registry-source-missing
  do
    let target := ctx.temporary / "registry-source-missing"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      return if (index == 1) then some row else none
  -- registry-source-duplicate
  do
    let target := ctx.temporary / "registry-source-duplicate"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun _ row => some row
    let path := target / "references/tasaki-2020.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "TASAKI2020\tfixture.pdf\t2020.ed1\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tpass1\tfixture\n")
  -- registry-source-bad-identity
  do
    let target := ctx.temporary / "registry-source-bad-identity"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 0 "OTHER"
      return if (true) then some row else none
  -- registry-post-source-missing
  do
    let target := ctx.temporary / "registry-post-source-missing"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      return if (index == 1) then some row else none
  -- registry-post-source-alternate
  do
    let target := ctx.temporary / "registry-post-source-alternate"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 0 "OTHER"
      return if (true) then some row else none
  -- registry-bootstrap-edition-pending
  do
    let target := ctx.temporary / "registry-bootstrap-edition-pending"
    copyFixture ctx good target
    replace target "phase.tsv" #["phase","bootstrap"]
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 2 "pending"
        row := row.set! 3 ""
        row := row.set! 4 ""
        row := row.set! 5 "pending"
      return if (true) then some row else none
  -- registry-bootstrap-source-frozen
  do
    let target := ctx.temporary / "registry-bootstrap-source-frozen"
    copyFixture ctx good target
    replace target "phase.tsv" #["phase","bootstrap"]
    for table in #["pages.tsv","claims.tsv","slices.tsv","bindings.tsv","claim-context.tsv","axioms.tsv","claim-axioms.tsv","statement-modules.tsv","statement-imports.tsv"] do
      headerOnly target table
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 5 "pending"
      return if (true) then some row else none
  -- registry-post-edition-pending
  do
    let target := ctx.temporary / "registry-post-edition-pending"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 2 "pending"
      return if (true) then some row else none
  -- registry-skeleton-frozen
  do
    let target := ctx.temporary / "registry-skeleton-frozen"
    copyFixture ctx good target
    replace target "phase.tsv" #["phase","skeleton"]
    editFile target "registry/axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 7 "3333333333333333333333333333333333333333"
      return if (true) then some row else none
  -- registry-skeleton-pending-axiom
  do
    let target := ctx.temporary / "registry-skeleton-pending-axiom"
    copyFixture ctx (ctx.temporary / "registry-skeleton-frozen") target
    editFile target "registry/axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 7 "PENDING"
      return if (true) then some row else none

/-- Construct the registry-skeleton-bad-axiom-oid through registry-census-source-extra-row counterfactuals. -/
def cases5 (ctx : Context) (good censusRoot : FilePath) : IO Unit := do
  -- registry-skeleton-bad-axiom-oid
  do
    let target := ctx.temporary / "registry-skeleton-bad-axiom-oid"
    copyFixture ctx (ctx.temporary / "registry-skeleton-frozen") target
    editFile target "registry/axioms.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 7 "not-an-object-id"
      return if (true) then some row else none
  -- registry-skeleton-pending-type
  do
    let target := ctx.temporary / "registry-skeleton-pending-type"
    copyFixture ctx (ctx.temporary / "registry-skeleton-frozen") target
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 6 "PENDING"
      return if (true) then some row else none
  -- registry-skeleton-pending-value
  do
    let target := ctx.temporary / "registry-skeleton-pending-value"
    copyFixture ctx (ctx.temporary / "registry-skeleton-frozen") target
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 7 "PENDING"
      return if (true) then some row else none
  -- registry-skeleton-pending-proof
  do
    let target := ctx.temporary / "registry-skeleton-pending-proof"
    copyFixture ctx (ctx.temporary / "registry-skeleton-frozen") target
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 10 "PENDING"
      return if (true) then some row else none
  -- registry-skeleton-pending-nonvacuity
  do
    let target := ctx.temporary / "registry-skeleton-pending-nonvacuity"
    copyFixture ctx (ctx.temporary / "registry-skeleton-frozen") target
    editFile target "registry/bindings.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 12 "LatticeSystem.Claims.Front.nonvacuity0001"
        row := row.set! 13 "PENDING"
      return if (true) then some row else none
  -- registry-source-mixed-width
  do
    let target := ctx.temporary / "registry-source-mixed-width"
    copyFixture ctx good target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 4 "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
      return if (true) then some row else none
  -- registry-census-source-identity
  do
    let target := ctx.temporary / "registry-census-source-identity"
    copyFixture ctx censusRoot target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 3 "bad"
      return if (true) then some row else none
  -- registry-census-source-bad-header
  do
    let target := ctx.temporary / "registry-census-source-bad-header"
    copyFixture ctx censusRoot target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 1 then
        row := ("bad".splitOn "\t").toArray
      return if (true) then some row else none
  -- registry-census-source-header-only
  do
    let target := ctx.temporary / "registry-census-source-header-only"
    copyFixture ctx censusRoot target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      return if (index == 1) then some row else none
  -- registry-census-source-extra-row
  do
    let target := ctx.temporary / "registry-census-source-extra-row"
    copyFixture ctx censusRoot target
    editFile target "references/tasaki-2020.tsv" fun _ row => some row
    let path := target / "references/tasaki-2020.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "OTHER\tfixture2.pdf\t2020.ed1\t5555555555555555555555555555555555555555\t6666666666666666666666666666666666666666\tfrozen\tfixture\n")

/-- Construct the registry-census-source-malformed-column through registry-census-page-id counterfactuals. -/
def cases6 (ctx : Context) (censusRoot : FilePath) : IO Unit := do
  -- registry-census-source-malformed-column
  do
    let target := ctx.temporary / "registry-census-source-malformed-column"
    copyFixture ctx censusRoot target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.extract 0 6
      return if (true) then some row else none
  -- registry-census-source-reserved-edition
  do
    let target := ctx.temporary / "registry-census-source-reserved-edition"
    copyFixture ctx censusRoot target
    editFile target "references/tasaki-2020.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 2 "pending"
      return if (true) then some row else none
  -- registry-census-claim-count
  do
    let target := ctx.temporary / "registry-census-claim-count"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun _ row => some row
    let path := target / "registry/claims.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0003\tTASAKI2020\t000002.0002\tPG-TASAKI2020-0002\textra\tassertion\tunnumbered_obligation\tExtra.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n")
  -- registry-census-claim-inactive
  do
    let target := ctx.temporary / "registry-census-claim-inactive"
    copyFixture ctx (ctx.temporary / "registry-census-claim-count") target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 11 "true"
        row := row.set! 12 "CL-TASAKI2020-0003"
        row := row.set! 13 "duplicate"
        row := row.set! 14 "review-1"
      return if (true) then some row else none
  -- registry-census-claim-superseded
  do
    let target := ctx.temporary / "registry-census-claim-superseded"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 12 "CL-TASAKI2020-0002"
      return if (true) then some row else none
  -- registry-census-equation-duplicate
  do
    let target := ctx.temporary / "registry-census-equation-duplicate"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun _ row => some row
    let path := target / "registry/claims.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0003\tTASAKI2020\t000001.0002\tPG-TASAKI2020-0001\tPDF p. 1; print p. NONE; NONE; equation (F.1)\tassertion\tequation\tDuplicate.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n")
    let records ← table target "claims.tsv"
    writeTable target "claims.tsv" #[records[0]!,records[1]!,records[3]!,records[2]!]
  -- registry-census-claims-empty
  do
    let target := ctx.temporary / "registry-census-claims-empty"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      return if (index == 1) then some row else none
  -- registry-census-skeleton-claim-axioms
  do
    let target := ctx.temporary / "registry-census-skeleton-claim-axioms"
    copyFixture ctx (ctx.temporary / "registry-census-skeleton-axioms") target
    editFile target "registry/claim-axioms.tsv" fun _ row => some row
    let path := target / "registry/claim-axioms.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0001\tAX-PROJECT-0002\n")
  -- registry-census-skeleton-claim-axioms-diagnostic
  do
    let target := ctx.temporary / "registry-census-skeleton-claim-axioms-diagnostic"
    copyFixture ctx censusRoot target
    editFile target "registry/claim-axioms.tsv" fun _ row => some row
    let path := target / "registry/claim-axioms.tsv"
    IO.FS.writeFile path ((← IO.FS.readFile path) ++ "CL-TASAKI2020-0001\tAX-TASAKI2020-0001\n")
  -- registry-census-page-id
  do
    let target := ctx.temporary / "registry-census-page-id"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 0 "PG-TASAKI2020-0003"
      return if (true) then some row else none
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 3 "PG-TASAKI2020-0003"
      return if (true) then some row else none

/-- Construct the registry-census-page-source through registry-census-claim-source counterfactuals. -/
def cases7 (ctx : Context) (censusRoot : FilePath) : IO Unit := do
  -- registry-census-page-source
  do
    let target := ctx.temporary / "registry-census-page-source"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 1 "OTHER"
      return if (true) then some row else none
  -- registry-census-page-order
  do
    let target := ctx.temporary / "registry-census-page-order"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 2 "000003"
      return if (true) then some row else none
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 2 "000003.0001"
      return if (true) then some row else none
  -- registry-census-page-pdf
  do
    let target := ctx.temporary / "registry-census-page-pdf"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 4 "3"
      return if (true) then some row else none
  -- registry-census-page-printed
  do
    let target := ctx.temporary / "registry-census-page-printed"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 3 ""
      return if (true) then some row else none
  -- registry-census-page-section
  do
    let target := ctx.temporary / "registry-census-page-section"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 5 ""
      return if (true) then some row else none
  -- registry-census-page-kind
  do
    let target := ctx.temporary / "registry-census-page-kind"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 6 ""
      return if (true) then some row else none
  -- registry-census-page-pass1
  do
    let target := ctx.temporary / "registry-census-page-pass1"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 7 "pending"
      return if (true) then some row else none
  -- registry-census-page-pass2
  do
    let target := ctx.temporary / "registry-census-page-pass2"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 8 "pending"
      return if (true) then some row else none
  -- registry-census-page-oid
  do
    let target := ctx.temporary / "registry-census-page-oid"
    copyFixture ctx censusRoot target
    editFile target "registry/pages.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 9 "PENDING"
      return if (true) then some row else none
  -- registry-census-claim-source
  do
    let target := ctx.temporary / "registry-census-claim-source"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 1 "OTHER"
      return if (true) then some row else none

/-- Construct the registry-census-claim-locator through registry-census-equation-label counterfactuals. -/
def cases8 (ctx : Context) (censusRoot : FilePath) : IO Unit := do
  -- registry-census-claim-locator
  do
    let target := ctx.temporary / "registry-census-claim-locator"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 4 ""
      return if (true) then some row else none
  -- registry-census-claim-content
  do
    let target := ctx.temporary / "registry-census-claim-content"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 3 then
        row := row.set! 7 ""
      return if (true) then some row else none
  -- registry-census-claim-page-order
  do
    let target := ctx.temporary / "registry-census-claim-page-order"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 3 "PG-TASAKI2020-0002"
      return if (true) then some row else none
  -- registry-census-claim-source-order
  do
    let target := ctx.temporary / "registry-census-claim-source-order"
    copyFixture ctx censusRoot target
    let records ← table target "claims.tsv"
    writeTable target "claims.tsv" #[records[0]!,records[2]!,records[1]!]
  -- registry-census-equation-label
  do
    let target := ctx.temporary / "registry-census-equation-label"
    copyFixture ctx censusRoot target
    editFile target "registry/claims.tsv" fun index original => Id.run do
      let mut row := original
      if index == 2 then
        row := row.set! 4 "PDF-p.1-equation-F.1"
      return if (true) then some row else none


/-- Header-only artifacts stay absent until a fixture explicitly introduces a registered R4 relation. -/
def censusArtifacts (ctx : Context) (censusRoot : FilePath) : IO Unit := do
  for (table,row) in #[
    ("slices","SL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001"),
    ("dependencies","CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\tfixture"),
    ("bindings","CL-TASAKI2020-0001\tLatticeSystem.Claims.Front.statement0001\tLatticeSystem.Claims.Front.claim0001\tLatticeSystem.Claims.Front\tdefinition\tproof_proposition\tPENDING\tPENDING\tproof_stub\ttheorem\tPENDING\tNONE\tNONE\tNONE\tCENSUS-FIXTURE-REVIEW"),
    ("axioms","AX-PROJECT-0002\tLatticeSystem.Axioms.State.fixture\tLatticeSystem.Axioms.State\tstate\tnot-applicable\trationale\treopen\tPENDING"),
    ("statement-modules","LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf")] do
    let target := ctx.temporary / ("registry-census-skeleton-" ++ table)
    copyFixture ctx censusRoot target
    add target (table ++ ".tsv") row
  add (ctx.temporary / "registry-census-skeleton-slices") "slices.tsv" "SL-TASAKI2020-0001\t2\tCL-TASAKI2020-0002"
  for table in #["bindings","statement-modules"] do
    let target := ctx.temporary / ("registry-census-skeleton-" ++ table)
    if table == "bindings" then add target "statement-modules.tsv" "LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf"
    add target "statement-modules.tsv" "LatticeSystem.Skeleton\tLatticeSystem/Skeleton.lean\tumbrella"

/-- Separate bootstrap negatives target each forbidden artifact before foreign-key validation. -/
def bootstrapArtifacts (ctx : Context) : IO Unit := do
  for (table,row) in #[
    ("claim-context","CL-TASAKI2020-0001\t1\tCL-TASAKI2020-0002\tassumption\tsame_item\tfixture"),
    ("statement-modules","LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf"),
    ("statement-imports","LatticeSystem.Claims.Front\t1\tMathlib\ttrue\tfalse\tfalse")] do
    let target := ctx.temporary / ("registry-bootstrap-" ++ table)
    copyFixture ctx (ctx.temporary / "registry-bootstrap-source-frozen") target
    add target (table ++ ".tsv") row

/-- The dedicated supersession baseline removes obsolete slices and bound proof artifacts. -/
def supersession (ctx : Context) (threeRoot target : FilePath) : IO Unit := do
  copyFixture ctx threeRoot target
  rewrite target "claims.tsv" fun index row =>
    if index == 4 then none else some <| if index == 2 then
      setFields row #[(11,"true"),(12,"CL-TASAKI2020-0002"),(13,"replacement-reason"),(14,"review-1")] else row
  rewrite target "slices.tsv" fun index row =>
    if index == 1 then some row else if index == 3 then some (row.set! 1 "1") else none
  headerOnly target "bindings.tsv"; headerOnly target "claim-axioms.tsv"

/-- Execute the original case metadata through actual native validators and mandatory oracles. -/
def runCases (ctx : Context) (middle : IO Unit) : IO Unit := do
  discard <| expect ctx "registry-good" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-good").toString]} ""
  discard <| expect ctx "duplicate-id" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-duplicate-id").toString]} ""
  discard <| expect ctx "bad-foreign-key" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-fk").toString]} ""
  discard <| expect ctx "bad-enum" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-enum").toString]} ""
  discard <| expect ctx "bad-order" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-order").toString]} ""
  discard <| expect ctx "bad-header" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-header").toString]} ""
  discard <| expect ctx "bad-column" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-column").toString]} ""
  discard <| expect ctx "control-character" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-control-char").toString]} ""
  discard <| expect ctx "bad-id" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-id").toString]} ""
  discard <| expect ctx "missing-page-coordinate" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-page-missing-coordinate").toString]} ""
  discard <| expect ctx "slice-duplicate" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-slice-duplicate").toString]} ""
  discard <| expect ctx "slice-position" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-slice-position").toString]} ""
  discard <| expect ctx "dependency-role" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-bad-role").toString]} ""
  discard <| expect ctx "dependency-order" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-order").toString]} ""
  discard <| expect ctx "dependency-cycle" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-cycle").toString]} ""
  discard <| expect ctx "dependency-self" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-self").toString]} ""
  discard <| expect ctx "dependency-duplicate" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-duplicate").toString]} ""
  discard <| expect ctx "dependency-rationale" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-rationale").toString]} ""
  discard <| expect ctx "fk-slice" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-fk-slice").toString]} ""
  discard <| expect ctx "fk-dependency" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-fk-dependency").toString]} ""
  discard <| expect ctx "fk-binding" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-fk-binding").toString]} ""
  discard <| expect ctx "fk-claim-axiom-claim" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-fk-claim-axiom-claim").toString]} ""
  discard <| expect ctx "fk-claim-axiom-axiom" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-fk-claim-axiom-axiom").toString]} ""
  discard <| expect ctx "supersession-registry-good" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-supersession-good").toString]} ""
  discard <| expect ctx "supersession-self" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-supersession-self").toString]} ""
  discard <| expect ctx "supersession-cycle" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-supersession-cycle").toString]} ""
  discard <| expect ctx "supersession-incoherent" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-supersession-incoherent").toString]} ""
  discard <| expect ctx "supersession-missing-rationale" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-supersession-missing-rationale").toString]} ""
  discard <| expect ctx "supersession-missing-review" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-supersession-missing-review").toString]} ""
  discard <| expect ctx "exclusion-good" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-exclusion-good").toString]} ""
  discard <| expect ctx "binding-out-of-scope" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-binding-out-of-scope").toString]} "out-of-scope claim has a binding"
  discard <| expect ctx "exclusion-missing-rationale" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-exclusion-missing-rationale").toString]} ""
  discard <| expect ctx "exclusion-missing-review" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-exclusion-missing-review").toString]} ""
  discard <| expect ctx "exclusion-incoherent" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-exclusion-incoherent").toString]} ""
  discard <| expect ctx "required-by-whitespace" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-whitespace").toString]} ""
  discard <| expect ctx "required-by-em-whitespace" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-dep-whitespace-em").toString]} ""
  discard <| expect ctx "remark-good" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-remark-good").toString]} ""
  discard <| expect ctx "bad-subkind" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bad-subkind").toString]} ""
  discard <| expect ctx "axiom-bad-category" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-axiom-bad-category").toString]} ""
  discard <| expect ctx "axiom-bad-path" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-axiom-bad-path").toString]} ""
  discard <| expect ctx "axiom-categories-good" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-axiom-categories-good").toString]} ""
  discard <| expect ctx "source-missing" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-source-missing").toString]} ""
  discard <| expect ctx "source-duplicate" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-source-duplicate").toString]} ""
  discard <| expect ctx "source-bad-identity" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-source-bad-identity").toString]} ""
  discard <| expect ctx "post-source-missing" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-post-source-missing").toString]} ""
  discard <| expect ctx "post-source-alternate" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-post-source-alternate").toString]} ""
  discard <| expect ctx "bootstrap-pending-edition" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bootstrap-edition-pending").toString]} ""
  discard <| expect ctx "bootstrap-source-frozen" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bootstrap-source-frozen").toString]} ""
  discard <| expect ctx "bootstrap-claim-context" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bootstrap-claim-context").toString]} "bootstrap requires header-only claim-context.tsv"
  discard <| expect ctx "bootstrap-statement-modules" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bootstrap-statement-modules").toString]} "bootstrap requires header-only statement-modules.tsv"
  discard <| expect ctx "bootstrap-statement-imports" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-bootstrap-statement-imports").toString]} "bootstrap requires header-only statement-imports.tsv"
  discard <| expect ctx "post-pending-edition" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-post-edition-pending").toString]} ""
  discard <| expect ctx "skeleton-frozen-oids" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-frozen").toString]} ""
  discard <| expect ctx "skeleton-pending-type" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-pending-type").toString]} "skeleton capability forbids pending binding OIDs"
  discard <| expect ctx "skeleton-pending-value" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-pending-value").toString]} "skeleton capability forbids pending binding OIDs"
  discard <| expect ctx "skeleton-pending-proof" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-pending-proof").toString]} "skeleton capability forbids pending binding OIDs"
  discard <| expect ctx "skeleton-pending-nonvacuity" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-pending-nonvacuity").toString]} "skeleton capability forbids pending binding OIDs"
  discard <| expect ctx "skeleton-pending-axiom" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-pending-axiom").toString]} "skeleton capability forbids pending axiom OIDs"
  discard <| expect ctx "skeleton-bad-axiom-oid" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-skeleton-bad-axiom-oid").toString]} "bad axiom type OID"
  discard <| expect ctx "source-mixed-oid-width" false {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-source-mixed-width").toString]} ""
  middle
  discard <| expect ctx "census-complete-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-good").toString]} ""
  discard <| expect ctx "census-complete" true {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-good").toString,"2","2","1"]} ""
  discard <| expect ctx "census-page-count" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-good").toString,"3","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-equation-count" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-good").toString,"2","2","2"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-source-identity" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-source-identity").toString,"2","2","1"]} "check-census: fixture source is not verified and frozen"
  discard <| expect ctx "census-source-bad-header" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-source-bad-header").toString,"2","2","1"]} "check-census: fixture source is not verified and frozen"
  discard <| expect ctx "census-source-header-only" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-source-header-only").toString,"2","2","1"]} "check-census: fixture source is not verified and frozen"
  discard <| expect ctx "census-source-extra-row" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-source-extra-row").toString,"2","2","1"]} "check-census: fixture source is not verified and frozen"
  discard <| expect ctx "census-source-malformed-column" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-source-malformed-column").toString,"2","2","1"]} "check-census: fixture source is not verified and frozen"
  discard <| expect ctx "census-source-reserved-edition" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-source-reserved-edition").toString,"2","2","1"]} "check-census: fixture source is not verified and frozen"
  discard <| expect ctx "census-claim-count-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-claim-count").toString]} ""
  discard <| expect ctx "census-claim-count" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-count").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claim-inactive-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-claim-inactive").toString]} ""
  discard <| expect ctx "census-claim-inactive" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-inactive").toString,"2","3","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claim-superseded" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-superseded").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-equation-duplicate-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-equation-duplicate").toString]} ""
  discard <| expect ctx "census-equation-duplicate" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-equation-duplicate").toString,"2","3","2"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claims-empty-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-claims-empty").toString]} ""
  discard <| expect ctx "census-claims-empty" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claims-empty").toString,"2","0","0"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-skeleton-slices-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-skeleton-slices").toString]} ""
  discard <| expect ctx "census-skeleton-slices" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-slices").toString,"2","2","1"]} "check-census: census requires header-only slices.tsv"
  discard <| expect ctx "census-skeleton-dependencies-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-skeleton-dependencies").toString]} ""
  discard <| expect ctx "census-skeleton-dependencies" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-dependencies").toString,"2","2","1"]} "check-census: census requires header-only dependencies.tsv"
  discard <| expect ctx "census-skeleton-bindings-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-skeleton-bindings").toString]} ""
  discard <| expect ctx "census-skeleton-bindings" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-bindings").toString,"2","2","1"]} "check-census: census requires header-only bindings.tsv"
  discard <| expect ctx "census-skeleton-axioms-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-skeleton-axioms").toString]} ""
  discard <| expect ctx "census-skeleton-axioms" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-axioms").toString,"2","2","1"]} "check-census: census requires header-only axioms.tsv"
  discard <| expect ctx "census-skeleton-statement-modules-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-skeleton-statement-modules").toString]} ""
  discard <| expect ctx "census-skeleton-statement-modules" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-statement-modules").toString,"2","2","1"]} "check-census: census requires header-only statement-modules.tsv"
  discard <| expect ctx "census-skeleton-claim-axioms-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-skeleton-claim-axioms").toString]} ""
  discard <| expect ctx "census-skeleton-claim-axioms-coupled" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-claim-axioms").toString,"2","2","1"]} "check-census: census requires header-only axioms.tsv"
  discard <| expect ctx "census-skeleton-claim-axioms-diagnostic" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-skeleton-claim-axioms-diagnostic").toString,"2","2","1"]} "check-census: census requires header-only claim-axioms.tsv"
  discard <| expect ctx "census-page-id-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-page-id").toString]} ""
  discard <| expect ctx "census-page-id" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-id").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-source" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-source").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-order-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-page-order").toString]} ""
  discard <| expect ctx "census-page-order" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-order").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-pdf-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-page-pdf").toString]} ""
  discard <| expect ctx "census-page-pdf" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-pdf").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-printed" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-printed").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-section" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-section").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-kind" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-kind").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-pass1-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-page-pass1").toString]} ""
  discard <| expect ctx "census-page-pass1" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-pass1").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-pass2-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-page-pass2").toString]} ""
  discard <| expect ctx "census-page-pass2" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-pass2").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-page-oid" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-page-oid").toString,"2","2","1"]} "check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
  discard <| expect ctx "census-claim-source" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-source").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claim-locator" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-locator").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claim-content" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-content").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claim-page-order-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-claim-page-order").toString]} ""
  discard <| expect ctx "census-claim-page-order" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-page-order").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-claim-source-order" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-claim-source-order").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
  discard <| expect ctx "census-equation-label-registry" true {ctx.gate "registry" ctx.temporary with args := #["--gate","registry",(ctx.temporary / "registry-census-equation-label").toString]} ""
  discard <| expect ctx "census-equation-label" false {ctx.gate "census" ctx.temporary with args := #["--gate","census","--fixture",(ctx.temporary / "registry-census-equation-label").toString,"2","2","1"]} "check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"

/-- Reproduce production-copy isolation, every structural case and the immutable-baseline oracle. -/
def run (ctx : Context) (middle : IO Unit := pure ()) : IO Unit := do
  let production := ctx.temporary / "production"
  copyRegistry ctx ctx.project production
  let baseline ← fingerprint ctx production
  discard <| checked (ctx.gate "registry" production)
  let good := ctx.temporary / "registry-good"
  legacy ctx production good
  let threeRoot := ctx.temporary / "legacy-three"
  three ctx good threeRoot
  let superRoot := ctx.temporary / "legacy-super"
  supersession ctx threeRoot superRoot
  let censusRoot := ctx.temporary / "registry-census-good"
  census ctx good censusRoot
  censusArtifacts ctx censusRoot
  cases0 ctx good threeRoot
  cases1 ctx threeRoot
  cases2 ctx good threeRoot superRoot
  cases3 ctx good
  cases4 ctx good
  cases5 ctx good censusRoot
  cases6 ctx censusRoot
  cases7 ctx censusRoot
  cases8 ctx censusRoot
  bootstrapArtifacts ctx
  let accepted ← ctx.accepted.get; let rejected ← ctx.rejected.get
  runCases ctx middle
  ensure ((← ctx.accepted.get) - accepted == 26 && (← ctx.rejected.get) - rejected == 89)
    "registry case inventory differs from 115 cases (26 positive, 89 rejection)"
  ensure ((← fingerprint ctx production) == baseline) "test-checkers: production baseline was mutated"
  IO.println "test-registry: ok (115 cases; 26 positive, 89 rejection cases)"

end Checker.Tests.Registry
