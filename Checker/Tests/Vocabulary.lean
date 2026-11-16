import Checker.Tests.Fixtures

/-! Registry and elaborated vocabulary counterfactuals, with actual kernel-environment inspection. -/
namespace Checker.Tests.Vocabulary
open System Checker.TestSupport Checker.Tests.Fixtures

/-- Vocabulary-review and census fixtures retain the live production corpus as their input. -/
def registry (ctx : Context) : IO Unit := do
  let good := ctx.temporary / "vocabulary-registry-good"
  copyRegistry ctx ctx.project good
  rewrite good "claim-vocabulary-review.tsv" fun index row =>
    some (if index == 1 then row else row.set! 2 "VOCABULARY-FIXTURE")
  discard <| checked (ctx.gate "registry" good)
  let clone := fun name => do
    let target := ctx.temporary / ("vocabulary-registry-" ++ name)
    copyFixture ctx good target
    pure target
  let uncovered ← clone "uncovered"
  rewrite uncovered "claim-vocabulary-review.tsv" fun index row => if index == 2 then none else some row
  discard <| expect ctx "uncovered" false (ctx.gate "registry" uncovered) "active claim lacks exactly one vocabulary review"
  let unused ← clone "unused"
  let vocabulary ← table unused "vocabulary.tsv"
  writeTable unused "vocabulary.tsv" <| #[vocabulary[0]!,#["VO-LS-00001","LatticeSystem.Vocabulary.Unused",
    "LatticeSystem.Vocabulary.Quantum","abbrev","primary","NONE","bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
    "cccccccccccccccccccccccccccccccccccccccc","linear_algebra","none"]] ++ vocabulary.extract 1 vocabulary.size
  discard <| expect ctx "unused" false (ctx.gate "registry" unused) "unused vocabulary declaration"
  let badImport ← clone "bad-import"
  mutateLine badImport "imports.tsv" 2 #[(2,"Lean.Meta")]
  discard <| expect ctx "bad-import" false (ctx.gate "registry" badImport) "unauthorized external import"
  let slices ← clone "slices"
  add slices "slices.tsv" "SL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001"
  add slices "slices.tsv" "SL-TASAKI2020-0002\t1\tCL-TASAKI2020-0002"
  discard <| expect ctx "slices" false (ctx.gate "registry" slices) "vocabulary requires header-only slices.tsv"
  discard <| checked {ctx.gate "census" slices with args := #["--gate","census","--fixture",slices.toString]}
  let badCensus ← clone "census-bad"
  mutateLine badCensus "pages.tsv" 2 #[(7,"pending")]
  discard <| expect ctx "census-regression" false
    {ctx.gate "census" badCensus with args := #["--gate","census","--fixture",badCensus.toString,"2","2","1"]}
    "page census is not exact"
  IO.println "test-vocabulary-registry: ok"

/-- The exact declaration schema and original pinned expression fingerprints. -/
def vocabularyHeader : Array String := #["vocabulary_id","declaration","module","declaration_kind","origin",
  "parent_vocabulary_id","type_oid","declaration_oid","design_role","finiteness_scope"]

/-- Prepare one genuine module fixture, preserving the old semantic shape and imported dependencies. -/
def prepare (ctx : Context) (name : String) : IO FilePath := do
  let target := ctx.temporary / ("vocabulary-semantic-" ++ name)
  writeTable target "modules.tsv" #[#["module","source_path","role"],#["Fixture.Subject","Fixture/Subject.lean","umbrella"]]
  writeTable target "imports.tsv" #[#["module","position","imported_module","is_exported","is_meta","import_all"]]
  writeTable target "vocabulary.tsv" #[vocabularyHeader,#["VO-FIXTURE-0001","Fixture.Item","Fixture.Subject",
    "abbrev","primary","NONE","eda6899694a1d94c33f3b10aa4e8e71fe7970cd3","eedad8e975235d5b3d0801932bc9e971a4c2a5a3","fixture","none"]]
  let body := match name with
    | "volume-carrier" | "global-carrier" =>
      "/-- Finite-carrier semantic fixture. -/\nabbrev Item (α : Type) [Fintype α] : Nat := Fintype.card α"
    | "volume-finset" =>
      "/-- Explicit-volume semantic fixture. -/\nabbrev Item (volume : Finset Nat) : Nat := volume.card"
    | "axiom" => "/-- Forbidden axiom fixture. -/\naxiom Item : Nat"
    | "body" => "/-- Body drift fixture. -/\nabbrev Item := Int"
    | "extra" => "/-- Registered fixture. -/\nabbrev Item := Nat\n/-- Unregistered fixture. -/\nabbrev Extra := Nat"
    | "sorry" => "/-- Sorry fixture. -/\ndef Item : Nat := by sorry"
    | "theorem" => "/-- Theorem fixture. -/\ntheorem Item : True := trivial"
    | "structure" => "/-- Structure fixture. -/\nstructure Pair where\n  left : Nat\n  right : Nat"
    | "transitive" => "/-- Transitive dependency fixture. -/\ndef Item : Nat := Mathlib.hidden"
    | _ => "/-- Harmless semantic-checker fixture. -/\nabbrev Item := Nat"
  if name == "transitive" then
    write target "Mathlib/FixtureDependency.lean" "module\n\n@[expose] public section\n\nnamespace Mathlib\n\n/-- Hidden unresolved dependency. -/\ndef hidden : Nat := by sorry\n\nend Mathlib\n"
  let imported := if name == "import" then "Mathlib.Data.Nat.Basic"
    else if name == "transitive" then "Mathlib.FixtureDependency"
    else if name == "volume-carrier" || name == "global-carrier" then "Mathlib.Data.Fintype.Card"
    else if name == "volume-finset" then "Mathlib.Data.Finset.Card"
    else "Init"
  if #["volume-carrier","global-carrier","volume-finset"].contains name then
    writeTable target "imports.tsv" #[#["module","position","imported_module","is_exported","is_meta","import_all"],
      #["Fixture.Subject","1",imported,"true","false","false"]]
  write target "Fixture/Subject.lean" ("module\n\npublic import " ++ imported ++ "\n\n@[expose] public section\n\nnamespace Fixture\n\n" ++ body ++ "\n\nend Fixture\n")
  return target

/-- All positive and negative vocabulary environment cases use actual elaboration and the shared driver. -/
def semantic (ctx : Context) : IO Unit := do
  let names := #["good","structure","axiom","extra","import","sorry","theorem","type","body","missing","module","graph","finiteness","transitive",
    "volume-carrier","volume-finset","volume-missing","global-carrier"]
  let fixtures ← names.foldlM (fun (fixtures : Std.HashMap String FilePath) name => do
    pure (fixtures.insert name (← prepare ctx name))) {}
  let get := fun name => fixtures[name]!
  for name in #["axiom","sorry"] do
    mutateLine (get name) "vocabulary.tsv" 2 #[(3,"definition"),(6,"471dd3a050827d736f2fc6858b2dc396f864af71"),(7,"PENDING")]
  for name in #["extra","import"] do mutateLine (get name) "vocabulary.tsv" 2 #[(7,"PENDING")]
  mutateLine (get "theorem") "vocabulary.tsv" 2 #[(3,"definition"),(6,"e05a1983e371947c14bd3b353ce23e5230136ffe"),(7,"PENDING")]
  mutateLine (get "type") "vocabulary.tsv" 2 #[(6,"0000000000000000000000000000000000000000"),(7,"PENDING")]
  mutateLine (get "missing") "vocabulary.tsv" 2 #[(1,"Fixture.Missing")]
  mutateLine (get "module") "vocabulary.tsv" 2 #[(2,"Fixture.Other")]
  mutateLine (get "graph") "vocabulary.tsv" 2 #[(8,"graph_core")]
  mutateLine (get "finiteness") "vocabulary.tsv" 2 #[(9,"local_operation")]
  for name in #["volume-carrier","global-carrier"] do
    mutateLine (get name) "vocabulary.tsv" 2
      #[(6,"72698f08016cb7babfc35eda2e6c2a4ca31f5987"),(7,"657484c93956c2e375e29c45aee640adbc681554")]
  mutateLine (get "volume-finset") "vocabulary.tsv" 2
    #[(6,"d917bcc3f1884a0edb4311dcd2665b3f081f1da3"),(7,"c371c8ef0aa6a1b92ff451ea11e12be2cc36ae3f")]
  for name in #["volume-carrier","volume-finset","volume-missing"] do
    mutateLine (get name) "vocabulary.tsv" 2 #[(9,"explicit_finite_volume")]
  writeTable (get "structure") "vocabulary.tsv" #[vocabularyHeader,
    #["VO-FIXTURE-0001","Fixture.Pair","Fixture.Subject","structure","primary","NONE","eda6899694a1d94c33f3b10aa4e8e71fe7970cd3","0586bd493d684bcfdfadaa8ff4947f51eec7c48e","fixture","none"],
    #["VO-FIXTURE-0002","Fixture.Pair.left","Fixture.Subject","projection","generated","VO-FIXTURE-0001","09117ddb3ec4f41df783154859883a9de3d050e2","dd7d0075df1dd47237fddb4cca34b753916ce4bb","generated","inherited"],
    #["VO-FIXTURE-0003","Fixture.Pair.mk","Fixture.Subject","constructor","generated","VO-FIXTURE-0001","70175a16711a85717984d042c516015d987420a8","9fff138066c2a8c1f2806a98d48afaa072024658","generated","inherited"],
    #["VO-FIXTURE-0004","Fixture.Pair.rec","Fixture.Subject","recursor","generated","VO-FIXTURE-0001","a0e3a5ba971ba56e66b0a2cf7a38ee6dab0137ef","83977b98a8d306caafe0acc5c6e163b7969eaeca","generated","inherited"],
    #["VO-FIXTURE-0005","Fixture.Pair.right","Fixture.Subject","projection","generated","VO-FIXTURE-0001","09117ddb3ec4f41df783154859883a9de3d050e2","f379ffda38c34d4b3959edf8c48281993ce88661","generated","inherited"]]
  mutateLine (get "transitive") "vocabulary.tsv" 2 #[(3,"definition"),(6,"PENDING"),(7,"PENDING")]
  writeTable (get "transitive") "modules.tsv" #[#["module","source_path","role"],
    #["Mathlib.FixtureDependency","Mathlib/FixtureDependency.lean","leaf"],#["Fixture.Subject","Fixture/Subject.lean","umbrella"]]
  writeTable (get "transitive") "imports.tsv" #[#["module","position","imported_module","is_exported","is_meta","import_all"],
    #["Fixture.Subject","1","Mathlib.FixtureDependency","true","false","false"]]
  for name in #["good","structure","volume-carrier","volume-finset"] do
    discard <| expect ctx name true (ctx.command "vocabulary" #["--fixture",(get name).toString])
  for name in #["axiom","extra","import","sorry","theorem","type","body","missing","module","graph","finiteness"] do
    discard <| expect ctx name false (ctx.command "vocabulary" #["--fixture",(get name).toString])
  discard <| expect ctx "transitive" false (ctx.command "vocabulary" #["--fixture",(get "transitive").toString])
    "transitive sorryAx dependency: Fixture.Item"
  discard <| expect ctx "volume-missing" false
    (ctx.command "vocabulary" #["--fixture",(get "volume-missing").toString])
    "explicit_finite_volume declaration lacks a finite carrier or Finset data: Fixture.Item"
  discard <| expect ctx "global-carrier" false
    (ctx.command "vocabulary" #["--fixture",(get "global-carrier").toString])
    "global vocabulary declaration requires Fintype: Fixture.Item"
  IO.println "test-vocabulary-semantic: ok"

end Checker.Tests.Vocabulary
