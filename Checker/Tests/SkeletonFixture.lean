import Checker.Tests.Fixtures

/-! Shared unmodified source skeleton and exact dump-derived fixture operations. -/
namespace Checker.Tests.SkeletonFixture
open System Checker.TestSupport Checker.Tests.Fixtures

/-- The reviewed setup declaration used by the common source skeleton. -/
def setup : Array String := #["/-- Reviewed setup proposition. -/", "def Setup : Prop := False", ""]

/-- The reviewed primary proposition retaining its setup antecedent. -/
def statement : Array String := #["/-- Reviewed proposition using its setup as an antecedent. -/", "def Statement : Prop := Setup → False", ""]

/-- The single registered proof stub and its declaration-local warning exception. -/
def proof : Array String := #["set_option warningAsError false in", "/-- Registered direct proof hole. -/", "theorem StatementProof : Statement := by sorry", ""]

/-- A real inhabitation witness, independent of any assumed statement proof. -/
def nonvacuity : Array String := #["/-- Explicit inhabitation witness for the fixture statement. -/", "theorem StatementNonvacuity : Nonempty Statement := ⟨fun h => h⟩", ""]

/-- Preserve whole-module terminal bytes and explicit public import order. -/
def writeModule (root : FilePath) (relative : String) (imports body : Array String) : IO Unit := do
  let lines := #["module", ""] ++ imports.map ("public import " ++ ·) ++
    #["", "@[expose] public section", "", "namespace Fixture", ""] ++ body ++ #["end Fixture"]
  write root relative (String.intercalate "\n" lines.toList ++ "\n")

/-- Write the complete claim module against its actual narrow core import. -/
def writeClaims (root : FilePath) (body : Array String) : IO Unit :=
  writeModule root "Fixture/Claims.lean" #["Mathlib.Init"] body

/-- Clone an independent fixture under a stable owned case identity. -/
def clone (ctx : Context) (source : FilePath) (name : String) : IO FilePath := do
  let target := ctx.temporary / name
  copyFixture ctx source target
  pure target

/-- Apply child-only dump and source-checker overrides to explicit fixture mode. -/
def command (ctx : Context) (target : FilePath) (dump : Option FilePath := none)
    (checker : Option FilePath := none) : Command :=
  let base := ctx.command "skeleton" #["--fixture", target.toString]
  let environment := match dump with | some path => base.env.push ("LATTICE_SKELETON_ACTUAL_OUT", some path.toString) | none => base.env
  let environment := match checker with | some path => environment.push ("LATTICE_SKELETON_CHECKER_DIR", some path.toString) | none => environment
  {base with env := environment}

/-- Report the actual first reached diagnostic, not merely a negative process status. -/
def reportReached (label diagnostic output : String) : IO Unit := do
  let some line := (output.splitOn "\n").find? (fun line => (line.splitOn diagnostic).length > 1)
    | throw <| IO.userError ("missing reached diagnostic for " ++ label)
  IO.println (label ++ "\t" ++ line)

/-- Run a pure skeleton case and retain the actual reached negative diagnostic. -/
def check (ctx : Context) (label : String) (positive : Bool) (target : FilePath)
    (diagnostic : String := "") (dump : Option FilePath := none) (checker : Option FilePath := none) : IO Unit := do
  let output ← expect ctx label positive (command ctx target dump checker) diagnostic
  unless positive do reportReached label diagnostic output

/-- Harvest actual environment output even when later validation intentionally rejects the fixture. -/
def harvest (ctx : Context) (target dump : FilePath) : IO Unit := do
  discard <| Checker.TestSupport.run (command ctx target (some dump))
  ensure (← dump.pathExists) ("no environment dump harvested from " ++ target.toString)
  ensure (!(← IO.FS.readFile dump).isEmpty) ("empty environment dump from " ++ target.toString)

/-- Read an exact declaration object identity from the actual skeleton dump. -/
def declarationOid (dump : FilePath) (declaration : String) (column : Nat) : IO String := do
  let rows := rowsOf (← IO.FS.readFile dump)
  let values := rows.filter fun row => row[1]?.getD "" == declaration
  ensure (values.size == 1) ("no unique object ID for " ++ declaration)
  let value := values[0]![column]!
  ensure (value.length == 40 && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')))
    ("invalid object ID for " ++ declaration)
  pure value

/-- Freeze all four binding identities from actual dump records and reject any remaining wildcard. -/
def freezeBindings (root dump : FilePath) : IO Unit := do
  let actual := rowsOf (← IO.FS.readFile dump)
  rewrite root "bindings.tsv" fun index row => some <| Id.run do
      if index == 1 then return row
      let row := match actual.find? (fun data => data[1]?.getD "" == row[1]!) with
        | some primary => row |>.set! 6 primary[3]! |>.set! 7 primary[4]!
        | none => row
      let row := if row[2]! == "NONE" then row else
        match actual.find? (fun data => data[1]?.getD "" == row[2]!) with
        | some proof => row.set! 10 proof[3]!
        | none => row
      let row := if row[12]! == "NONE" then row else
        match actual.find? (fun data => data[1]?.getD "" == row[12]!) with
        | some witness => row.set! 13 witness[3]!
        | none => row
      return row
  ensure (((← IO.FS.readFile (root / "registry/bindings.tsv")).splitOn "PENDING").length == 1)
    "frozen bindings still carry a wildcard OID"

/-- Create the common source skeleton without pure-only harvesting or composed-project setup. -/
def good (ctx : Context) : IO FilePath := do
  let root := ctx.temporary / "good"
  newTarget ctx root
  IO.FS.createDirAll (root / "Fixture")
  replace root "phase.tsv" #[
    "phase",
    "skeleton",
  ]
  replace root "sources.tsv" #[
    "source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage",
    "SRA\tTR-A\t1\tbook\tA\tA\tA\t2026\ted1\tnone\tNONE\tNONE\ta\tref\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tfrozen",
    "SRB\tTR-B\t1\tpaper\tB\tB\tB\t2026\ted1\tnone\tNONE\tNONE\tb\tref\t3333333333333333333333333333333333333333\t4444444444444444444444444444444444444444\tfrozen",
  ]
  replace root "source-progress.tsv" #[
    "source_id\tlifecycle\treview_ref",
    "SRA\tskeleton_frozen\tfixture-review",
    "SRB\tvocabulary_reviewed\tfixture-review",
  ]
  replace root "claims.tsv" #[
    "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref",
    "CL-SRA-0001\tSRA\t000001.0001\tPG-SRA-0001\tfixture setup\tdefinition\tdefinition\tSetup.\t1111111111111111111111111111111111111111\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE",
    "CL-SRA-0002\tSRA\t000001.0002\tPG-SRA-0001\tfixture assertion\tassertion\ttheorem\tAssertion.\t2222222222222222222222222222222222222222\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE",
    "CL-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tstaged later source\tassertion\ttheorem\tLater.\t3333333333333333333333333333333333333333\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE",
  ]
  replace root "item-claims.tsv" #[
    "item_id\tposition\tclaim_id",
    "IT-SRA-0001\t1\tCL-SRA-0001",
    "IT-SRA-0001\t2\tCL-SRA-0002",
    "IT-SRB-0001\t1\tCL-SRB-0001",
  ]
  replace root "dependencies.tsv" #[
    "claim_id\trole\ttarget_claim_id\trationale",
  ]
  replace root "claim-context.tsv" #[
    "claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref",
    "CL-SRA-0002\t1\tCL-SRA-0001\tassumption\tsame_item\tfixture-review",
  ]
  replace root "bindings.tsv" #[
    "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref",
    "CL-SRA-0001\tFixture.Setup\tNONE\tFixture.Claims\tdefinition\tdefinition_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tfixture-review",
    "CL-SRA-0002\tFixture.Statement\tFixture.StatementProof\tFixture.Claims\tdefinition\tproof_proposition\tPENDING\tPENDING\tproof_stub\ttheorem\tPENDING\tNONE\tNONE\tNONE\tfixture-review",
  ]
  replace root "axioms.tsv" #[
    "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid",
  ]
  replace root "claim-axioms.tsv" #[
    "claim_id\taxiom_id",
  ]
  replace root "vocabulary.tsv" #[
    "vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope",
  ]
  replace root "claim-vocabulary.tsv" #[
    "claim_id\tvocabulary_id",
  ]
  replace root "claim-vocabulary-review.tsv" #[
    "claim_id\tbasis\treview_ref",
    "CL-SRA-0001\tmathlib_only\tfixture-review",
    "CL-SRA-0002\tmathlib_only\tfixture-review",
    "CL-SRB-0001\tmathlib_only\tfixture-review",
  ]
  replace root "modules.tsv" #[
    "module\tsource_path\trole",
    "Fixture.Production\tFixture/Production.lean\troot",
  ]
  replace root "imports.tsv" #[
    "module\tposition\timported_module\tis_exported\tis_meta\timport_all",
    "Fixture.Production\t1\tMathlib.Init\ttrue\tfalse\tfalse",
  ]
  replace root "statement-modules.tsv" #[
    "module\tsource_path\trole",
    "Fixture.Claims\tFixture/Claims.lean\tleaf",
    "Fixture.Skeleton\tFixture/Skeleton.lean\tumbrella",
  ]
  replace root "statement-imports.tsv" #[
    "module\tposition\timported_module\tis_exported\tis_meta\timport_all",
    "Fixture.Claims\t1\tMathlib.Init\ttrue\tfalse\tfalse",
    "Fixture.Skeleton\t1\tFixture.Claims\ttrue\tfalse\tfalse",
  ]
  write root "Fixture/Production.lean" "module\n\npublic import Mathlib.Init\n\n/-! Production fixture. -/\n"
  writeClaims root (setup ++ statement ++ proof)
  write root "Fixture/Skeleton.lean" "module\n\npublic import Fixture.Claims\n\n/-! Skeleton fixture umbrella. -/\n"
  pure root

/-- Remove only the exact checker-infrastructure suffix from an owned mathematical counterfactual. -/
def minimalLake (ctx : Context) (root : FilePath) : IO Unit := do
  ctx.owned root
  let text ← IO.FS.readFile (root / "lakefile.toml")
  let suffix := "\n# Verification infrastructure is an explicit target, separate from the mathematical default.\n[[lean_lib]]\nname = \"Checker\"\n\n[[lean_exe]]\nname = \"checker\"\nroot = \"Checker.Main\"\n"
  let parts := text.splitOn suffix
  ensure (parts.length == 2 && parts[1]! == "") "counterfactual checker infrastructure suffix changed"
  let originalPrefix := parts[0]!
  ensure (originalPrefix.endsWith "\n[[lean_lib]]\nname = \"LatticeSystem\"\n")
    "counterfactual mathematical library prefix changed"
  write root "lakefile.toml" originalPrefix

end Checker.Tests.SkeletonFixture
