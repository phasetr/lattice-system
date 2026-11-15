import Checker.Tests.SkeletonFixture
import Checker.Tests.FixtureSupport

/-! Production-composed skeleton regressions over an owned minimal canonical project. -/
namespace Checker.Tests.SkeletonComposed
open System Lean Checker.TestSupport Checker.Tests.Fixtures Checker.Tests.SkeletonFixture
open Checker.Tests.FixtureSupport (property jsonArray jsonString)

/-- Read one strict JSON array of TSV fields without escaping or normalization changes. -/
def jsonRow (value : Json) : IO (Array String) := do
  (← jsonArray value).mapM jsonString

/-- Run the generator's unchanged canonical inventory derivation through its read-only typed CLI. -/
def deriveItems (ctx : Context) (root : FilePath) : IO Unit := do
  ctx.owned root
  let output ← checked (ctx.docs #["--derive-source-items","--root",root.toString])
  let value ← match Json.parse output with | .ok value => pure value | .error error => throw <| IO.userError error
  ensure ((← property value "version") == toJson (1 : Nat)) "source-item derivation protocol version"
  for (key, name) in #[("source_items","source-items.tsv"),("item_claims","item-claims.tsv")] do
    let data ← property value key
    let header ← jsonRow (← property data "header")
    ensure (header == (← table root name)[0]!) "canonical source-item derivation header"
    let rows ← (← jsonArray (← property data "rows")).mapM jsonRow
    writeTable root name (#[header] ++ rows)

/-- Refresh claim field identities and every source's exact ordered census from real fixture bytes. -/
def refreshProduction (ctx : Context) (root : FilePath) : IO Unit := do
  let claims ← table root "claims.tsv"
  let rows ← claims.zipIdx |>.mapM fun (row,index) => do
    if index == 0 then pure row else pure (row.set! 8 (← blob ctx row[7]!))
  writeTable root "claims.tsv" rows
  let header := (← table root "source-invariants.tsv")[0]!
  let pages ← table root "pages.tsv"
  let invariants := #["SRA","SRB"].map fun source =>
    #[source,toString (pages.filter fun row => row[1]?.getD "" == source).size,
      "0","0","0","0","PENDING","FIXTURE-REVIEW"]
  writeTable root "source-invariants.tsv" (#[header] ++ invariants)
  refresh ctx root

/-- Invoke the unchanged public generator on the independently owned canonical fixture. -/
def generator (ctx : Context) (root : FilePath) (mode : String) : IO String :=
  checked (ctx.docs #[mode,"--root",root.toString])

/-- Run the actual nine native gates, vocabulary, renderer, fixture build and skeleton in original order. -/
def productionGates (ctx : Context) (root : FilePath) : IO Unit := do
  ctx.owned root
  for name in #["tree","schema","sources","order","lifecycle","registry","census","source-items","policy"] do
    IO.print (← checked (ctx.gate name root))
  IO.print (← checked (ctx.command "vocabulary" #[root.toString]))
  IO.print (← generator ctx root "--check")
  let toolchain := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  IO.print (← checked ⟨"lake",#["build"],root,#[ ("ELAN_TOOLCHAIN",some toolchain)]⟩)
  IO.print (← checked (ctx.command "skeleton" #[root.toString]))

/-- Count one composed pipeline while reporting the actual diagnostic reached by each rejection. -/
def checkComposed (ctx : Context) (label : String) (positive : Bool) (root : FilePath)
    (diagnostic : String := "") : IO Unit := do
  let action := do
    try productionGates ctx root
    catch error =>
      unless positive do reportReached label diagnostic error.toString
      throw error
  expectAction ctx label positive action diagnostic "skeleton-composed"

/-- Count one direct production skeleton guard without running earlier composed gates. -/
def checkProduction (ctx : Context) (label : String) (root : FilePath) (diagnostic : String) : IO Unit := do
  let output ← expect ctx label false (ctx.command "skeleton" #[root.toString]) diagnostic
  reportReached label diagnostic output

/-- Apply an exact textual Lake configuration mutation with no host or dependency changes. -/
def lakeText (root : FilePath) (change : String → String) : IO Unit := do
  let path := root / "lakefile.toml"
  IO.FS.writeFile path (change (← IO.FS.readFile path))

/-- Exercise typed/default diagnostic policy, weak options and package/library raw argument rejection. -/
def diagnosticCases (ctx : Context) (production : FilePath) : IO Unit := do
  for variant in #["package-warning","package-linter","library-warning","library-linter","unknown-weak","missing-warning","typed-true"] do
    let root ← clone ctx production ("production-diagnostic-" ++ variant)
    lakeText root fun text =>
      if variant == "missing-warning" then text.replace "warningAsError = true\n" ""
      else if variant == "typed-true" then (text.replace "warningAsError = true" "warningAsError = \"true\"") ++ "leanOptions = [[\"warningAsError\", \"true\"]]\n"
      else if variant == "package-warning" then text.replace "warningAsError = true" "warningAsError = false"
      else if #["package-linter","unknown-weak"].contains variant then
        let name := if variant == "package-linter" then "unusedVariables" else "fixtureMissing"
        let extra := "weak.linter." ++ name ++ " = false\n" ++
          (if variant == "unknown-weak" then "pp.universes = false\nmaxRecDepth = 4096\n" else "")
        text.replace "[[require]]" (extra ++ "\n[[require]]")
      else if variant == "library-warning" then text ++ "leanOptions = [[\"warningAsError\", false]]\n"
      else text ++ "leanOptions = [[\"weak.linter.unusedVariables\", false]]\n"
    if #["unknown-weak","typed-true"].contains variant then
      checkComposed ctx ("production-diagnostic-" ++ variant ++ "-gates") true root
    else if variant == "missing-warning" then
      checkComposed ctx "production-diagnostic-missing-warning" false root "Lake warningAsError is not enabled in package"
    else
      checkProduction ctx ("production-diagnostic-" ++ variant) root
        (if variant.endsWith "warning" then "Lake diagnostic option disables warningAsError" else "Lake diagnostic option disables linter.unusedVariables")
  for owner in #["package","library"] do
    for field in #["moreLeanArgs","weakLeanArgs"] do
      let name := "production-diagnostic-" ++ owner ++ "-" ++ field
      let root ← clone ctx production name
      let extra := field ++ " = [\"-DwarningAsError=false\"]"
      lakeText root fun text => if owner == "package" then
        text.replace "defaultTargets = [\"LatticeSystem\"]" ("defaultTargets = [\"LatticeSystem\"]\n" ++ extra)
        else text ++ extra ++ "\n"
      checkProduction ctx name root ("Lake raw Lean arguments are unsupported in " ++ owner)

/-- Check exact default module selection, physical source identity and unsupported Lake dependencies. -/
def lakeCases (ctx : Context) (production : FilePath) : IO Unit := do
  for (variant, extra, positive, diagnostic) in #[
      ("safe-roots","roots = [\"LatticeSystem\", \"LatticeSystem.Vocabulary\"]",true,""),
      ("safe-globs","roots = [\"LatticeSystem\", \"LatticeSystem.Skeleton\"]\nglobs = [\"LatticeSystem\", \"LatticeSystem.Vocabulary\"]",true,""),
      ("skeleton-roots","roots = [\"LatticeSystem\", \"LatticeSystem.Skeleton\"]",false,"default library selects a statement or unregistered module"),
      ("skeleton-globs","globs = [\"LatticeSystem.*\"]",false,"default library selects a statement or unregistered module"),
      ("package-deps","extraDepTargets = [\"LatticeSystem.Skeleton\"]",false,"package extraDepTargets is unsupported"),
      ("library-deps","extraDepTargets = [\"LatticeSystem.Skeleton\"]",false,"library needs/extraDepTargets is unsupported"),
      ("library-needs","needs = [\"+LatticeSystem.Skeleton\"]",false,"library needs/extraDepTargets is unsupported"),
      ("facets","defaultFacets = [\"static\"]",false,"default library facets must be leanArts"),
      ("source-path","srcDir = \"alternate\"",false,"default module source differs from registry")] do
    let root ← clone ctx production ("production-lake-" ++ variant)
    lakeText root fun text => if variant == "package-deps" then
      text.replace "defaultTargets = [\"LatticeSystem\"]" ("defaultTargets = [\"LatticeSystem\"]\n" ++ extra)
      else text ++ extra ++ "\n"
    if variant == "source-path" then
      write root "alternate/LatticeSystem.lean" (← IO.FS.readFile (root / "LatticeSystem.lean"))
    if positive then checkComposed ctx ("production-lake-" ++ variant ++ "-gates") true root
    else checkProduction ctx ("production-lake-" ++ variant) root diagnostic
  for owner in #["package","library"] do
    for field in #["dynlibs","plugins"] do
      let name := "production-lake-" ++ owner ++ "-" ++ field
      let root ← clone ctx production name
      let extra := field ++ " = [\"+LatticeSystem.Skeleton:dynlib\"]"
      lakeText root fun text => if owner == "package" then
        text.replace "defaultTargets = [\"LatticeSystem\"]" ("defaultTargets = [\"LatticeSystem\"]\n" ++ extra)
        else text ++ extra ++ "\n"
      checkProduction ctx name root (owner ++ " " ++ field ++ " is unsupported")
/-- Create an owned physical-provider alias without following any existing symbolic link. -/
def linkSource (ctx : Context) (root : FilePath) (relative : String) (source : FilePath) : IO Unit := do
  ctx.owned root
  let destination := root / relative
  if let some parent := destination.parent then IO.FS.createDirAll parent
  discard <| checked ⟨"ln",#["-s",source.toString,destination.toString],ctx.project,#[]⟩

/-- Check shadow vocabulary/statement providers and harmless aliases of every registered module. -/
def providerCases (ctx : Context) (production : FilePath) : IO Unit := do
  let shadow ← clone ctx production "production-lake-shadow-vocabulary"
  linkSource ctx shadow ".lake/shadow-source/LatticeSystem.lean" (shadow / "LatticeSystem.lean")
  write shadow ".lake/shadow-source/LatticeSystem/Vocabulary.lean"
    "module\n\npublic import Mathlib.Init\n\nset_option warningAsError false in\n/-- Unregistered theorem hidden behind a different physical provider. -/\ntheorem UnregisteredShadow : True := by sorry\n"
  lakeText shadow (· ++ "srcDir = \".lake/shadow-source\"\n")
  checkProduction ctx "production-lake-shadow-vocabulary" shadow "Lake vocabulary provider source differs from registry"
  let aliasRoot ← clone ctx production "production-lake-alias-source"
  for name in #["modules.tsv","statement-modules.tsv"] do
    let rows ← table aliasRoot name
    for row in rows.extract 1 rows.size do
      linkSource ctx aliasRoot (".lake/alias-source/" ++ row[1]!) (aliasRoot / row[1]!)
  lakeText aliasRoot (· ++ "srcDir = \".lake/alias-source\"\n")
  checkComposed ctx "production-lake-alias-source-gates" true aliasRoot
  let statementShadow ← clone ctx aliasRoot "production-lake-shadow-statement"
  for name in #["modules.tsv","statement-modules.tsv"] do
    let rows ← table statementShadow name
    for row in rows.extract 1 rows.size do
      IO.FS.removeFile (statementShadow / ".lake/alias-source" / row[1]!)
      linkSource ctx statementShadow (".lake/alias-source/" ++ row[1]!) (statementShadow / row[1]!)
  let leaf := "LatticeSystem/Claims/Front.lean"
  IO.FS.removeFile (statementShadow / ".lake/alias-source" / leaf)
  write statementShadow (".lake/alias-source/" ++ leaf) ((← IO.FS.readFile (statementShadow / leaf)) ++
    "\nset_option warningAsError false in\n/-- Unregistered theorem in an alternate statement provider. -/\ntheorem UnregisteredShadowStatement : True := by sorry\n")
  checkProduction ctx "production-lake-shadow-statement" statementShadow "Lake statement provider source differs from registry"

/-- Check frozen OID policy, imports, warning ownership, inactive contexts and proof-stage policy through composed gates. -/
def productionPolicyCases (ctx : Context) (production : FilePath) : IO Unit := do
  for (variant, diagnostic) in #[("pending","skeleton capability forbids pending binding OIDs"),
      ("frozen-oid","wrong type OID"),("any","bad statement type OID"),
      ("imports","statement import registry/environment mismatch"),("warning","unscoped warningAsError suppression"),
      ("inactive-owner","inactive claim-context owner or target"),("inactive-target","inactive claim-context owner or target"),
      ("proof-policy","production policy is not implemented for proof")] do
    let root ← clone ctx production ("production-" ++ variant)
    if #["pending","frozen-oid","any"].contains variant then
      mutateLine root "bindings.tsv" 2 #[(6,if variant == "pending" then "PENDING" else if variant == "any" then "ANY" else "0000000000000000000000000000000000000000")]
    else if variant == "imports" then mutateLine root "statement-imports.tsv" 2 #[(3,"false")]
    else if variant == "warning" then
      let path := "LatticeSystem/Claims/Front.lean"
      write root path ((← IO.FS.readFile (root / path)) ++ "set_option warningAsError false -- file-wide exception\n")
    else if variant == "proof-policy" then replace root "phase.tsv" #["phase","proof"]
    else
      let inactive := if variant == "inactive-target" then "CL-SRA-0001" else "CL-SRB-0001"
      rewrite root "claims.tsv" fun _ row => some <| if row[0]! == inactive then
        setFields row #[(11,"true"),(12,"CL-SRA-0002"),(13,"fixture-duplicate"),(14,"FIXTURE-REVIEW")] else row
      for name in #["bindings.tsv","claim-vocabulary-review.tsv"] do
        rewrite root name fun _ row => if row[0]! == inactive then none else some row
      if variant == "inactive-owner" then mutateLine root "claim-context.tsv" 2 #[(0,"CL-SRB-0001"),(4,"inherited")]
      refreshProduction ctx root
    checkComposed ctx ("production-" ++ variant) false root diagnostic

/-- Freeze vocabulary identities from the vocabulary checker's actual machine-readable dump. -/
def freezeVocabulary (root : FilePath) (dump : String) : IO Unit := do
  let actual := rowsOf dump
  rewrite root "vocabulary.tsv" fun line row =>
    if line == 1 then some row else
      match actual.find? (fun data => data[1]?.getD "" == row[1]!) with
      | some data => some (row |>.set! 6 data[4]! |>.set! 7 data[5]!)
      | none => some (row |>.set! 6 "" |>.set! 7 "")
  ensure (((← IO.FS.readFile (root / "registry/vocabulary.tsv")).splitOn "PENDING").length == 1)
    "frozen vocabulary retains a pending identity"

/-- Exercise real primary-type/value vocabulary references and independently missing claim admissions. -/
def vocabularyCases (ctx : Context) (production : FilePath) : IO Unit := do
  let root ← clone ctx production "production-vocabulary"
  write root "LatticeSystem/VocabularyData.lean" "module\n\npublic import Mathlib.Init\n\n@[expose] public section\n\nnamespace LatticeSystem\n/-- First counterfactual vocabulary carrier. -/\ndef Ground : Type := Nat\n\n/-- Second counterfactual vocabulary carrier. -/\ndef AlternateGround : Type := Nat\n\nend LatticeSystem\n"
  write root "LatticeSystem/Vocabulary.lean" "module\n\npublic import LatticeSystem.VocabularyData\n\n/-! Counterfactual vocabulary umbrella. -/\n"
  add root "modules.tsv" "LatticeSystem.VocabularyData\tLatticeSystem/VocabularyData.lean\tleaf"
  mutate root "imports.tsv" "LatticeSystem.Vocabulary" 2 "LatticeSystem.VocabularyData"
  add root "imports.tsv" "LatticeSystem.VocabularyData\t1\tMathlib.Init\ttrue\tfalse\tfalse"
  add root "statement-imports.tsv" "LatticeSystem.Claims.Front\t2\tLatticeSystem.VocabularyData\ttrue\tfalse\tfalse"
  add root "vocabulary.tsv" "VO-LS-9001\tLatticeSystem.Ground\tLatticeSystem.VocabularyData\tdefinition\tprimary\tNONE\tPENDING\tPENDING\tstat_mech\tnone"
  add root "vocabulary.tsv" "VO-LS-9002\tLatticeSystem.AlternateGround\tLatticeSystem.VocabularyData\tdefinition\tprimary\tNONE\tPENDING\tPENDING\tstat_mech\tnone"
  for row in #["CL-SRA-0001\tVO-LS-9001","CL-SRA-0002\tVO-LS-9001","CL-SRA-0002\tVO-LS-9002"] do add root "claim-vocabulary.tsv" row
  rewrite root "claim-vocabulary-review.tsv" fun _ row => some <| if row[0]!.startsWith "CL-SRA-" then row.set! 1 "project_vocabulary" else row
  mutateLine root "claim-context.tsv" 2 #[(3,"term_reference")]
  mutate root "bindings.tsv" "CL-SRA-0001" 5 "definition_value"
  write root "LatticeSystem/Claims/Front.lean" "module\n\npublic import Mathlib.Init\npublic import LatticeSystem.VocabularyData\n\n@[expose] public section\n\nnamespace LatticeSystem.Claims.Front\n/-- Primary type directly uses reviewed vocabulary. -/\ndef Setup (x : LatticeSystem.Ground) : Nat := x\n\n/-- Primary value directly uses reviewed vocabulary and an earlier setup. -/\ndef Statement : Prop :=\n  ∀ (x : LatticeSystem.Ground) (y : LatticeSystem.AlternateGround), Setup x = y\n\nset_option warningAsError false in\n/-- Registered counterfactual direct proof hole. -/\ntheorem StatementProof : Statement := by sorry\n\nend LatticeSystem.Claims.Front\n"
  let dump ← checked (ctx.command "vocabulary" #["--dump","--fixture",root.toString])
  freezeVocabulary root dump
  let bindingsDump := ctx.temporary / "production-vocabulary-binding-dump.tsv"
  harvest ctx root bindingsDump
  let rows := rowsOf (← IO.FS.readFile bindingsDump)
  ensure (rows.any fun row => row[1]?.getD "" == "LatticeSystem.Claims.Front.Setup" &&
    (row[8]!.splitOn ",").contains "LatticeSystem.Ground") "primary type vocabulary use was not observed"
  ensure (rows.any fun row => row[1]?.getD "" == "LatticeSystem.Claims.Front.Statement" &&
    (row[9]!.splitOn ",").contains "LatticeSystem.Ground" && (row[9]!.splitOn ",").contains "LatticeSystem.AlternateGround")
    "primary value vocabulary uses were not observed"
  freezeBindings root bindingsDump
  discard <| generator ctx root "--write"
  discard <| git root #["add","--","LatticeSystem","registry","docs"]
  let mathlibBasis ← clone ctx root "production-vocabulary-mathlib-basis"
  mutate mathlibBasis "claim-vocabulary-review.tsv" "CL-SRA-0001" 1 "mathlib_only"
  rewrite mathlibBasis "claim-vocabulary.tsv" fun _ row => if row[0]! == "CL-SRA-0001" then none else some row
  let unadmitted ← clone ctx root "production-vocabulary-unadmitted"
  rewrite unadmitted "claim-vocabulary.tsv" fun _ row => if row[0]! == "CL-SRA-0002" && row[1]! == "VO-LS-9002" then none else some row
  add unadmitted "claim-vocabulary.tsv" "CL-SRB-0001\tVO-LS-9002"
  mutate unadmitted "claim-vocabulary-review.tsv" "CL-SRB-0001" 1 "project_vocabulary"
  for target in #[mathlibBasis,unadmitted] do discard <| generator ctx target "--write"
  checkComposed ctx "production-vocabulary-gates" true root
  checkComposed ctx "production-vocabulary-mathlib-basis" false mathlibBasis "primary project vocabulary contradicts claim review basis"
  checkComposed ctx "production-vocabulary-unadmitted" false unadmitted "primary vocabulary use lacks claim-vocabulary admission"
/-- Materialize the live candidate index and build a canonical project from the unmodified common GOOD fixture. -/
def prepare (ctx : Context) (goodRoot : FilePath) : IO FilePath := do
  let root := ctx.temporary / "production-composed"
  copyCandidate ctx root
  ctx.owned root
  minimalLake ctx root
  IO.FS.removeDirAll (root / "LatticeSystem")
  IO.FS.createDirAll (root / "LatticeSystem/Claims")
  for entry in ← (root / "registry").readDir do
    if entry.fileName.endsWith ".tsv" then headerOnly root entry.fileName
  for entry in ← (goodRoot / "registry").readDir do
    if entry.fileName.endsWith ".tsv" then
      IO.FS.writeBinFile (root / "registry" / entry.fileName) (← IO.FS.readBinFile entry.path)
  let replaceData := fun name rows => do
    let header := (← table root name)[0]!
    writeTable root name (#[header] ++ rows)
  replaceData "tracks.tsv" #[#["TR-A","1","Fixture A","a"],#["TR-B","2","Fixture B","b"]]
  replaceData "pages.tsv" #[#["PG-SRA-0001","SRA","000001","1","1","1","content","complete","complete",String.ofList (List.replicate 40 'a')],
    #["PG-SRB-0001","SRB","000001","1","1","1","content","complete","complete",String.ofList (List.replicate 40 'b')]]
  rewrite root "claims.tsv" fun line row => some (if line == 1 then row else row.set! 4 "PDF p. 1; paragraph 1")
  deriveItems ctx root
  replaceData "claim-vocabulary-review.tsv" (#["CL-SRA-0001","CL-SRA-0002","CL-SRB-0001"].map fun id => #[id,"mathlib_only","FIXTURE-REVIEW"])
  replaceData "modules.tsv" #[#["LatticeSystem","LatticeSystem.lean","root"],#["LatticeSystem.Vocabulary","LatticeSystem/Vocabulary.lean","umbrella"]]
  replaceData "imports.tsv" #[#["LatticeSystem","1","LatticeSystem.Vocabulary","true","false","false"],#["LatticeSystem.Vocabulary","1","Mathlib.Init","true","false","false"]]
  replaceData "statement-modules.tsv" #[#["LatticeSystem.Claims.Front","LatticeSystem/Claims/Front.lean","leaf"],#["LatticeSystem.Skeleton","LatticeSystem/Skeleton.lean","umbrella"]]
  replaceData "statement-imports.tsv" #[#["LatticeSystem.Claims.Front","1","Mathlib.Init","true","false","false"],#["LatticeSystem.Skeleton","1","LatticeSystem.Claims.Front","true","false","false"]]
  let bindings ← IO.FS.readFile (root / "registry/bindings.tsv")
  write root "registry/bindings.tsv" ((bindings.replace "Fixture.Claims" "LatticeSystem.Claims.Front").replace "Fixture." "LatticeSystem.Claims.Front.")
  let source ← IO.FS.readFile (goodRoot / "Fixture/Claims.lean")
  write root "LatticeSystem/Claims/Front.lean" ((source.replace "namespace Fixture" "namespace LatticeSystem.Claims.Front").replace "end Fixture" "end LatticeSystem.Claims.Front")
  write root "LatticeSystem/Vocabulary.lean" "module\n\npublic import Mathlib.Init\n\n/-! Counterfactual declaration-free vocabulary umbrella. -/\n"
  write root "LatticeSystem/Skeleton.lean" "module\n\npublic import LatticeSystem.Claims.Front\n\n/-! Counterfactual skeleton umbrella. -/\n"
  let packages ← IO.FS.realPath (ctx.project / ".lake/packages")
  linkSource ctx root ".lake/packages" packages
  refreshProduction ctx root
  let dump := ctx.temporary / "production-dump.tsv"
  harvest ctx root dump
  freezeBindings root dump
  discard <| generator ctx root "--write"
  discard <| git root #["add","-A"]
  pure root

/-- Run only the thirty-nine composed production cases; pure fixtures and harvesting are not constructed. -/
def run (ctx : Context) : IO Unit := do
  let passed ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let goodRoot ← good ctx
  let initial ← fingerprint ctx goodRoot
  let production ← prepare ctx goodRoot
  checkComposed ctx "production-composed-gates" true production
  diagnosticCases ctx production
  lakeCases ctx production
  providerCases ctx production
  productionPolicyCases ctx production
  vocabularyCases ctx production
  ensure ((← fingerprint ctx goodRoot) == initial) "composed cases changed the shared GOOD registry"
  ensure ((← ctx.accepted.get) - passed == 7 && (← ctx.rejected.get) - rejected == 32)
    "skeleton composed matrix differs from 39 cases (7 positive, 32 negative)"
  IO.println "test-skeleton-composed: ok (39 cases; 7 positive, 32 negative)"

end Checker.Tests.SkeletonComposed
