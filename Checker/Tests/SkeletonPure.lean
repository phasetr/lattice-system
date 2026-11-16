import Checker.Tests.SkeletonFixture

/-! Pure skeleton semantic regressions, independent of composed production setup. -/
namespace Checker.Tests.SkeletonPure
open System Checker.TestSupport Checker.Tests.Fixtures Checker.Tests.SkeletonFixture

/-- Create a fresh case with a complete replacement claim module. -/
def withClaims (ctx : Context) (source : FilePath) (name : String) (body : Array String) : IO FilePath := do
  let root ← clone ctx source name
  writeClaims root body
  pure root

/-- Verify genuine nonvacuity, reducible wrappers and universe-exact proof obligations. -/
def propositionCases (ctx : Context) (goodRoot : FilePath) : IO FilePath := do
  check ctx "good" true goodRoot
  let dependency ← clone ctx goodRoot "dependency"
  headerOnly dependency "claim-context.tsv"
  add dependency "dependencies.tsv" "CL-SRA-0002\trequires\tCL-SRA-0001\tNONE"
  check ctx "dependency-admitted" true dependency
  let nv ← withClaims ctx goodRoot "nonvacuity" (setup ++ statement ++ proof ++ nonvacuity)
  mutateLine nv "bindings.tsv" 3 #[(12,"Fixture.StatementNonvacuity"),(13,"PENDING")]
  check ctx "nonvacuity-good" true nv
  for (name, body, diagnostic) in #[
      ("nonvacuity-true", #["/-- True surrogate offered as nonvacuity. -/", "theorem StatementNonvacuity : True := trivial", ""], "nonvacuity declaration concludes True"),
      ("nonvacuity-self", #["/-- Self-fulfilling statement offered as nonvacuity. -/", "theorem StatementNonvacuity (h : Statement) : Statement := h", ""], "nonvacuity declaration follows from its own hypotheses"),
      ("nonvacuity-id-conclusion", #["/-- Self-fulfilling obligation behind a reducible conclusion wrapper. -/", "theorem StatementNonvacuity (h : Statement) : id Statement := h", ""], "nonvacuity declaration follows from its own hypotheses"),
      ("nonvacuity-id-hypothesis", #["/-- Self-fulfilling obligation behind a reducible hypothesis wrapper. -/", "theorem StatementNonvacuity (h : id Statement) : Statement := h", ""], "nonvacuity declaration follows from its own hypotheses"),
      ("nonvacuity-unrelated", #["/-- Unrelated triviality offered as nonvacuity. -/", "theorem StatementNonvacuity : (1 : Nat) = 1 := rfl", ""], "nonvacuity declaration does not reference its bound statement"),
      ("nonvacuity-conjunct", #["/-- Hypothesis restated beside a True conjunct. -/", "theorem StatementNonvacuity (h : Statement) : Statement ∧ True := ⟨h, trivial⟩", ""], "nonvacuity declaration follows from its own hypotheses")] do
    let root ← withClaims ctx nv name (setup ++ statement ++ proof ++ body)
    check ctx name false root diagnostic
  let wrapped ← clone ctx nv "nonvacuity-wrapped"
  add wrapped "claims.tsv" "CL-SRA-0003\tSRA\t000001.0003\tPG-SRA-0001\tfixture wrapper\tdefinition\tdefinition\tWrapper.\t5555555555555555555555555555555555555555\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE"
  add wrapped "item-claims.tsv" "IT-SRA-0001\t3\tCL-SRA-0003"
  add wrapped "bindings.tsv" "CL-SRA-0003\tFixture.SelfFulfilling\tNONE\tFixture.Claims\tdefinition\tdefinition_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tfixture-review"
  add wrapped "dependencies.tsv" "CL-SRA-0003\trequires\tCL-SRA-0002\tNONE"
  writeClaims wrapped (setup ++ statement ++ proof ++ #["/-- Reviewed wrapper around a self-implication. -/", "def SelfFulfilling : Prop := Statement → Statement", "",
    "/-- Self-implication offered as nonvacuity through a wrapper. -/", "theorem StatementNonvacuity (h : Statement) : SelfFulfilling := fun _ => h", ""])
  check ctx "nonvacuity-wrapped" false wrapped "nonvacuity declaration follows from its own hypotheses"
  let irreducible ← withClaims ctx wrapped "nonvacuity-irreducible" (setup ++ statement ++ proof ++ #[
    "/-- Reviewed irreducible wrapper around a self-implication. -/", "@[irreducible] def SelfFulfilling : Prop := Statement → Statement", "",
    "/-- Self-implication hidden behind an irreducible definition. -/", "theorem StatementNonvacuity (h : Statement) : SelfFulfilling := by", "  delta SelfFulfilling", "  exact fun _ => h", ""])
  check ctx "nonvacuity-irreducible" false irreducible "nonvacuity declaration follows from its own hypotheses"
  let trueRoot ← withClaims ctx goodRoot "primary-irreducible-true" (#["/-- Reviewed irreducible proposition identity. -/",
    "@[irreducible] def Setup (p : Prop) : Prop := p", "", "/-- Literal True hidden behind the reviewed identity. -/", "def Statement : Prop := Setup True", ""] ++ proof)
  headerOnly trueRoot "claim-context.tsv"
  add trueRoot "dependencies.tsv" "CL-SRA-0002\trequires\tCL-SRA-0001\tNONE"
  check ctx "primary-irreducible-true" false trueRoot "literal True primary statement Fixture.Statement"
  let polymorphic := #["/-- Reviewed universe-polymorphic proposition. -/", "def Statement.{u} : Prop := ∀ (V : Type u), Setup → V = V", ""]
  let polymorphicTwo := #["/-- Reviewed proposition with two ordered universes. -/", "def Statement.{u, v} : Prop := ∀ (V : Type u) (W : Type v), Setup → V = V ∧ W = W", ""]
  for (variant, primary, comment, theoremText, positive) in #[
      ("one", polymorphic, "/-- Exact universally quantified proof hole. -/", "theorem StatementProof.{u} : Statement.{u} := by sorry", true),
      ("alpha-two", polymorphicTwo, "/-- Exact proof with alpha-renamed universe parameters. -/", "theorem StatementProof.{x, y} : Statement.{x, y} := by sorry", true),
      ("specialized", polymorphic, "/-- Specialized universe is not the universal obligation. -/", "theorem StatementProof : Statement.{0} := by sorry", false),
      ("reordered", polymorphicTwo, "/-- Reordered universes are not the bound order. -/", "theorem StatementProof.{x, y} : Statement.{y, x} := by sorry", false),
      ("duplicated", polymorphicTwo, "/-- Reusing one universe specializes the obligation. -/", "theorem StatementProof.{x} : Statement.{x, x} := by sorry", false)] do
    let name := "proof-universe-" ++ variant
    let root ← withClaims ctx goodRoot name (setup ++ primary ++ #["set_option warningAsError false in", comment, theoremText, ""])
    check ctx name positive root (if positive then "" else "proof type is not exactly the bound primary statement")
  pure nv

/-- Copy the actual semantic checker sources for source-substitution mutation controls. -/
def checkerCopy (ctx : Context) (name : String) : IO FilePath := do
  let target := ctx.temporary / name
  newTarget ctx target
  IO.FS.createDirAll (target / "Checker")
  for file in #["Semantic.lean","Skeleton.lean"] do
    IO.FS.writeBinFile (target / "Checker" / file) (← IO.FS.readBinFile (ctx.project / "Checker" / file))
  pure target

/-- Freeze actual declaration identities and verify both legitimate source copies and a value-encoding mutant. -/
def frozenCases (ctx : Context) (goodRoot nv : FilePath) : IO Unit := do
  let frozen ← clone ctx nv "frozen"
  let dump := ctx.temporary / "frozen-dump.tsv"
  harvest ctx frozen dump
  freezeBindings frozen dump
  check ctx "frozen-oids" true frozen
  for (name, col, diagnostic) in #[("frozen-statement-type",6,"wrong type OID Fixture.Statement"),
      ("frozen-statement-value",7,"wrong value OID Fixture.Statement"), ("frozen-proof-type",10,"wrong type OID Fixture.StatementProof"),
      ("frozen-nonvacuity",13,"wrong type OID Fixture.StatementNonvacuity")] do
    let root ← clone ctx frozen name
    mutateLine root "bindings.tsv" 3 #[(col,"0000000000000000000000000000000000000000")]
    check ctx name false root diagnostic
  let copy ← checkerCopy ctx "checker-copy"
  let mutant ← checkerCopy ctx "checker-mutant"
  let source ← IO.FS.readFile (mutant / "Checker/Skeleton.lean")
  ensure ((source.splitOn "valueEncoding info]").length == 2) "value-encoding mutation did not apply exactly once"
  IO.FS.writeFile (mutant / "Checker/Skeleton.lean") (source.replace "valueEncoding info]" "encodeExpr info.levelParams info.type]")
  check ctx "checker-copy" true frozen "" none (some copy)
  check ctx "value-encoding-mutant" false frozen "wrong value OID Fixture.Statement" none (some mutant)
  let axiomRoot ← clone ctx goodRoot "axiom-frozen"
  add axiomRoot "axioms.tsv" "AX-FIXTURE-0001\tFixture.interfaceAxiom\tFixture.Claims\tstate\tfixture\tfixture\treopen\tPENDING"
  add axiomRoot "claim-axioms.tsv" "CL-SRA-0002\tAX-FIXTURE-0001"
  let axiomProof := #["set_option warningAsError false in", "/-- Registered direct proof hole using the axiom. -/", "theorem StatementProof : Statement := by have := interfaceAxiom; sorry", ""]
  writeClaims axiomRoot (setup ++ statement ++ #["/-- Registered interface axiom. -/", "axiom interfaceAxiom : Setup", ""] ++ axiomProof)
  let axiomDump := ctx.temporary / "axiom-dump.tsv"
  harvest ctx axiomRoot axiomDump
  mutateLine axiomRoot "axioms.tsv" 2 #[(7,← declarationOid axiomDump "Fixture.interfaceAxiom" 3)]
  check ctx "axiom-frozen-type" true axiomRoot
  let unapproved ← clone ctx axiomRoot "axiom-unapproved-actual"
  headerOnly unapproved "claim-axioms.tsv"
  check ctx "axiom-unapproved-actual" false unapproved "unapproved claim axiom is used"
  let unused ← clone ctx axiomRoot "axiom-approved-unused"
  add unused "claim-axioms.tsv" "CL-SRA-0001\tAX-FIXTURE-0001"
  check ctx "axiom-approved-unused" false unused "approved claim axiom is not used"
  let restated ← withClaims ctx axiomRoot "axiom-restated" (setup ++ statement ++ #[
    "/-- Registered interface axiom restated as a stronger assertion. -/", "axiom interfaceAxiom : False", ""] ++ axiomProof)
  check ctx "axiom-restated" false restated "wrong type OID Fixture.interfaceAxiom"
/-- Check exact proof obligations and reviewed setup references in values and declaration types. -/
def contextCases (ctx : Context) (goodRoot : FilePath) : IO Unit := do
  for (name, comment, obligation) in #[("proof-disjunction","/-- Obligation weakened to a disjunction. -/","Statement ∨ True"),
      ("proof-implication","/-- Obligation weakened to a self-implication. -/","Statement → Statement"),
      ("proof-true","/-- Obligation weakened to True. -/","True")] do
    let term := if name == "proof-implication" then "fun _ => by sorry" else "by sorry"
    let root ← withClaims ctx goodRoot name (setup ++ statement ++ #["set_option warningAsError false in",comment,"theorem StatementProof : " ++ obligation ++ " := " ++ term,""])
    check ctx name false root "proof type is not exactly the bound primary statement"
  let forward ← withClaims ctx goodRoot "required-by" #[
    "/-- Reviewed proposition that stands alone. -/", "def Statement : Prop := False → False", "",
    "set_option warningAsError false in", "/-- Registered direct proof hole. -/", "theorem StatementProof : Statement := by sorry", "",
    "/-- Reviewed setup pulled forward from the later claim. -/", "def Setup : Prop := Statement → False", ""]
  headerOnly forward "claim-context.tsv"
  add forward "dependencies.tsv" "CL-SRA-0002\trequired_by\tCL-SRA-0001\tfrontier-exception"
  check ctx "required-by" true forward
  let backward ← clone ctx goodRoot "required-by-backward"
  headerOnly backward "claim-context.tsv"
  add backward "dependencies.tsv" "CL-SRA-0001\trequired_by\tCL-SRA-0002\tfrontier-exception"
  check ctx "required-by-backward" false backward "required_by reference does not pull a later claim forward"
  let typeRoot ← withClaims ctx goodRoot "type-context" (setup ++ statement ++ proof ++ #[
    "/-- Reviewed context datum whose setup use is in its type. -/", "def Context : Setup → False := False.elim", ""])
  add typeRoot "claims.tsv" "CL-SRA-0003\tSRA\t000001.0003\tPG-SRA-0001\tfixture context\tdefinition\tdefinition\tContext.\t5555555555555555555555555555555555555555\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE"
  add typeRoot "item-claims.tsv" "IT-SRA-0001\t3\tCL-SRA-0003"
  add typeRoot "bindings.tsv" "CL-SRA-0003\tFixture.Context\tNONE\tFixture.Claims\tdefinition\tdefinition_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tfixture-review"
  let unadmitted ← clone ctx typeRoot "type-context-unadmitted"
  add typeRoot "claim-context.tsv" "CL-SRA-0003\t1\tCL-SRA-0001\tassumption\tsame_item\tfixture-review"
  check ctx "type-context" true typeRoot
  check ctx "type-context-unadmitted" false unadmitted "actual setup reference lacks claim-context or dependency CL-SRA-0003"
  let letRoot ← withClaims ctx goodRoot "let-guard" (setup ++ #[
    "/-- Reviewed proposition mentioning its setup only in a let value. -/", "def Statement : Prop := let _s : Prop := Setup; False", ""] ++ proof)
  check ctx "let-guard" false letRoot "assumption context is not a binder or antecedent"
  for variant in #["duplicate-after","duplicate-before","duplicate-assumption-good","duplicate-term-good"] do
    let root ← clone ctx (if variant == "duplicate-assumption-good" then goodRoot else letRoot) ("context-" ++ variant)
    let first := if #["duplicate-before","duplicate-term-good"].contains variant then "term_reference" else "assumption"
    let last := if variant == "duplicate-before" then "assumption" else "term_reference"
    mutateLine root "claim-context.tsv" 2 #[(3,first)]
    add root "claim-context.tsv" ("CL-SRA-0002\t2\tCL-SRA-0001\t" ++ last ++ "\tsame_item\tfixture-review")
    let positive := variant.endsWith "good"
    check ctx ("context-" ++ variant) positive root (if positive then "" else "assumption context is not a binder or antecedent")

/-- Check binding inventory, declaration identity, shape, scope, isolation and direct proof-hole ownership. -/
def bindingCases (ctx : Context) (goodRoot : FilePath) : IO Unit := do
  let contract ← clone ctx goodRoot "contract"
  headerOnly contract "bindings.tsv"
  headerOnly contract "statement-modules.tsv"
  check ctx "contract" false contract "skeleton capability requires a registered skeleton"
  let missing ← clone ctx goodRoot "missing"
  rewrite missing "bindings.tsv" fun line row => if line == 3 then none else some row
  check ctx "missing" false missing "skeleton source lacks a binding"
  let duplicate ← clone ctx goodRoot "duplicate"
  let rows ← table duplicate "bindings.tsv"
  writeTable duplicate "bindings.tsv" (rows.extract 0 2 ++ #[rows[1]!] ++ rows.extract 2 rows.size)
  check ctx "duplicate" false duplicate "duplicate binding"
  for (name, file, line, fields, diagnostic) in #[
      ("count","claims.tsv",3,#[(5,"out_of_scope"),(9,"fixture-scope"),(10,"fixture-review")],"binding count does not match formalization targets"),
      ("name","bindings.tsv",3,#[(1,"Fixture.Missing")],"missing or wrong-module declaration"),
      ("module","bindings.tsv",3,#[(3,"Fixture.Skeleton")],"missing or wrong-module declaration"),
      ("kind","bindings.tsv",3,#[(4,"abbrev")],"wrong declaration kind"),
      ("oid","bindings.tsv",3,#[(6,"0000000000000000000000000000000000000000")],"wrong type OID")] do
    let root ← clone ctx goodRoot name
    mutateLine root file line fields
    check ctx name false root diagnostic
  let shape ← withClaims ctx goodRoot "shape" (#["/-- Reviewed setup datum. -/", "def Setup : Type := Nat", ""] ++ statement ++ proof)
  mutateLine shape "bindings.tsv" 2 #[(5,"proof_proposition")]
  check ctx "shape" false shape "proof proposition is not Prop-valued"
  let extra ← withClaims ctx goodRoot "extra" (setup ++ statement ++ proof ++ #["/-- Extra unregistered declaration. -/", "def Extra : Nat := 0", ""])
  check ctx "extra" false extra "extra declaration Fixture.Extra"
  let matchRoot ← withClaims ctx goodRoot "match" (setup ++ #["/-- Reviewed proposition written with a pattern match. -/",
    "def Statement : Prop := Setup → match (0 : Nat) with | 0 => False | _ + 1 => False", ""] ++ proof)
  check ctx "match" false matchRoot "extra declaration Fixture.Statement.match_1"
  let multiple ← withClaims ctx goodRoot "multiple" (setup ++ statement ++ #["set_option warningAsError false in",
    "/-- Two registered-looking holes in one stub. -/", "theorem StatementProof : Statement := by", "  have first : Statement := by sorry", "  have second : Statement := by sorry", "  exact first", ""])
  check ctx "multiple" false multiple "exactly one direct sorryAx"
  let hidden ← withClaims ctx goodRoot "hidden" (setup ++ statement ++ #["/-- Independently reviewed proposition. -/", "def Other : Prop := False → False", "",
    "set_option warningAsError false in", "/-- Registered direct proof hole. -/", "theorem OtherProof : Other := by sorry", "",
    "set_option warningAsError false in", "/-- Bound proof hides its hole behind another stub. -/", "theorem StatementProof : Statement := OtherProof", ""])
  add hidden "claims.tsv" "CL-SRA-0003\tSRA\t000001.0003\tPG-SRA-0001\tfixture hidden assertion\tassertion\ttheorem\tOther.\t5555555555555555555555555555555555555555\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE"
  add hidden "item-claims.tsv" "IT-SRA-0001\t3\tCL-SRA-0003"
  add hidden "bindings.tsv" "CL-SRA-0003\tFixture.Other\tFixture.OtherProof\tFixture.Claims\tdefinition\tproof_proposition\tPENDING\tPENDING\tproof_stub\ttheorem\tPENDING\tNONE\tNONE\tNONE\tfixture-review"
  check ctx "hidden" false hidden "hidden or transitive-only sorryAx"
  let context ← clone ctx goodRoot "context"
  headerOnly context "claim-context.tsv"
  check ctx "context" false context "actual setup reference lacks claim-context"
  let backward ← clone ctx goodRoot "backward"
  let rows ← table backward "claims.tsv"
  writeTable backward "claims.tsv" ((rows.set! 1 rows[2]!).set! 2 rows[1]!)
  check ctx "backward" false backward "statement references a claim that is not earlier"
  let umbrella ← clone ctx goodRoot "umbrella"
  rewrite umbrella "statement-imports.tsv" fun line row => if line <= 2 then some row else none
  write umbrella "Fixture/Skeleton.lean" "module\n\n/-! Skeleton fixture umbrella without its leaf. -/\n"
  check ctx "umbrella" false umbrella "umbrella misses"
  let leak ← clone ctx goodRoot "leak"
  write leak "Fixture/Production.lean" "module\n\npublic import Fixture.Claims\n\n/-! Leaking production fixture. -/\n"
  mutateLine leak "imports.tsv" 2 #[(2,"Fixture.Claims")]
  check ctx "leak" false leak "production root reaches"
  let axiomRoot ← withClaims ctx goodRoot "axiom" (setup ++ statement ++ proof ++ #["/-- Approved but unused axiom. -/", "axiom allowed : False", ""])
  add axiomRoot "axioms.tsv" "AX-FIXTURE-0001\tFixture.allowed\tFixture.Claims\tstate\tfixture\tfixture\tremove\tPENDING"
  check ctx "axiom" false axiomRoot "registered axiom is unused"
/-- Verify registered vocabulary and actual imported theorem/opaque/axiom traversal. -/
def vocabularyCases (ctx : Context) (goodRoot nv : FilePath) : IO Unit := do
  let vocabulary ← clone ctx goodRoot "vocabulary"
  writeModule vocabulary "Fixture/Vocab.lean" #["Mathlib.Init"] #["/-- Registered R3 vocabulary datum. -/", "def Ground : Prop := False", ""]
  add vocabulary "modules.tsv" "Fixture.Vocab\tFixture/Vocab.lean\tleaf"
  add vocabulary "imports.tsv" "Fixture.Vocab\t1\tMathlib.Init\ttrue\tfalse\tfalse"
  add vocabulary "statement-imports.tsv" "Fixture.Claims\t2\tFixture.Vocab\ttrue\tfalse\tfalse"
  add vocabulary "vocabulary.tsv" "VO-FX-0001\tFixture.Ground\tFixture.Vocab\tdefinition\tprimary\tNONE\tPENDING\tPENDING\tfixture\tnone"
  add vocabulary "claim-vocabulary.tsv" "CL-SRA-0002\tVO-FX-0001"
  mutate vocabulary "claim-vocabulary-review.tsv" "CL-SRA-0002" 1 "project_vocabulary"
  writeModule vocabulary "Fixture/Claims.lean" #["Mathlib.Init","Fixture.Vocab"] (setup ++ #["/-- Reviewed proposition naming registered vocabulary. -/", "def Statement : Prop := Setup → Ground", ""] ++ proof)
  let unregistered ← clone ctx vocabulary "vocabulary-unregistered"
  headerOnly unregistered "vocabulary.tsv"
  check ctx "registered-vocabulary" true vocabulary
  check ctx "vocabulary-unregistered" false unregistered "primary statement uses an unregistered project constant Fixture.Ground"
  let primary ← withClaims ctx goodRoot "nonstandard-primary-axiom" (#["set_option linter.deprecated false in",
    "/-- Unsupported kernel axiom in a negative primary fixture. -/", "def Setup : Prop := Lean.trustCompiler = True.intro", ""] ++ statement ++ proof)
  check ctx "nonstandard-primary-axiom" false primary "unregistered nonstandard axiom Lean.trustCompiler"
  let witness ← withClaims ctx nv "nonstandard-nonvacuity-axiom" (setup ++ statement ++ proof ++ #["set_option linter.deprecated false in",
    "/-- Unsupported kernel axiom in a negative nonvacuity fixture. -/", "theorem StatementNonvacuity : Nonempty Statement := ⟨fun h => (fun (_ : True) => h) Lean.trustCompiler⟩", ""])
  check ctx "nonstandard-nonvacuity-axiom" false witness "unregistered nonstandard axiom Lean.trustCompiler"
  let ordinary ← withClaims ctx nv "imported-ordinary-theorem" (setup ++ statement ++ proof ++ #[
    "/-- Witness whose proof value actually refers to an imported ordinary theorem. -/", "theorem StatementNonvacuity : Nonempty Statement := ⟨fun h => (fun (_ : 0 + 0 = 0) => h) (Nat.zero_add 0)⟩", ""])
  let ordinaryDump := ctx.temporary / "imported-theorem-dump.tsv"
  check ctx "imported-ordinary-theorem" true ordinary "" (some ordinaryDump)
  let rows := rowsOf (← IO.FS.readFile ordinaryDump)
  ensure (rows.any fun row => row[1]?.getD "" == "Fixture.StatementNonvacuity" &&
    (row[9]!.splitOn ",").contains "Nat.zero_add" && !(row[10]!.splitOn ",").contains "Nat.zero_add")
    "imported ordinary theorem was not actually referenced"
  let opaqueRoot ← withClaims ctx goodRoot "imported-opaque-axiom" (#["set_option linter.deprecated false in",
    "/-- Imported opaque wrapper concealing an unsupported kernel axiom. -/", "def Setup : Prop := Lean.reduceBool false = false", ""] ++ statement ++ proof)
  let opaqueDump := ctx.temporary / "imported-opaque-dump.tsv"
  check ctx "imported-opaque-axiom" false opaqueRoot "unregistered nonstandard axiom Lean.trustCompiler" (some opaqueDump)
  let rows := rowsOf (← IO.FS.readFile opaqueDump)
  ensure (rows.any fun row => row[1]?.getD "" == "Fixture.Setup" &&
    (row[9]!.splitOn ",").contains "Lean.reduceBool" && (row[10]!.splitOn ",").contains "Lean.trustCompiler")
    "imported opaque wrapper and its kernel axiom were not both visited"

/-- Check forbidden warning consumers and linter exemptions independently of registered proof exceptions. -/
def diagnosticCases (ctx : Context) (goodRoot : FilePath) : IO Unit := do
  let diagnosticSetup := #["/-- Setup whose unused argument normally emits a warning. -/", "def Setup (unused : Nat) : Prop := False", ""]
  let diagnosticStatement := #["/-- Proposition referring to that setup. -/", "def Statement : Prop := Setup 0 → False", ""]
  for (variant, body, diagnostic, positive) in #[
      ("guard-msgs", #["#guard_msgs (drop all) in"] ++ diagnosticSetup ++ diagnosticStatement ++ proof, "forbidden diagnostic suppression #guard_msgs", false),
      ("linter-command", #["set_option linter.unusedVariables false in"] ++ diagnosticSetup ++ diagnosticStatement ++ proof, "forbidden diagnostic suppression linter.unusedVariables", false),
      ("linter-file", #["set_option linter.unusedVariables false"] ++ diagnosticSetup ++ diagnosticStatement ++ proof, "forbidden diagnostic suppression linter.unusedVariables", false),
      ("linter-term", #["/-- A term-local linter exemption. -/", "def Setup : Prop := set_option linter.unusedVariables false in False", ""] ++ statement ++ proof, "forbidden diagnostic suppression linter.unusedVariables", false),
      ("linter-tactic", setup ++ statement ++ #["set_option warningAsError false in", "/-- A stub cannot disable an additional linter. -/", "theorem StatementProof : Statement := by", "  set_option linter.unusedVariables false in", "    sorry", ""], "forbidden diagnostic suppression linter.unusedVariables", false),
      ("nolint-inline", #["/-- A declaration-local environment linter exemption. -/", "@[nolint unusedArguments]", "def Setup : Prop := False", ""] ++ statement ++ proof, "forbidden diagnostic suppression nolint", false),
      ("nolint-command", setup ++ #["attribute [nolint unusedArguments] Setup"] ++ statement ++ proof, "forbidden diagnostic suppression nolint", false),
      ("warn-option", #["set_option warn.classDefReducibility false in"] ++ setup ++ statement ++ proof, "forbidden diagnostic suppression warn.classDefReducibility", false),
      ("harmless-options", #["set_option maxRecDepth 4096", "set_option pp.universes false in"] ++ setup ++ statement ++ proof, "", true),
      ("linter-grind", #["/-- Satisfiable setup for an unresolved grind fixture. -/", "def Setup : Prop := (0 : Nat) = 0", ""] ++ statement ++ #["set_option warningAsError false in", "/-- Registered direct hole using the distinct grind option syntax. -/", "theorem StatementProof : Statement := by", "  grind (abstractProof := false) =>", "    set_option warningAsError false in", "      set_option linter.unusedVariables false in", "        sorry", ""], "forbidden diagnostic suppression linter.unusedVariables", false),
      ("linter-conv", setup ++ statement ++ #["set_option warningAsError false in", "/-- Registered stub with a nested ordinary tactic option. -/", "theorem StatementProof : Statement := by", "  conv =>", "    tactic =>", "      set_option linter.unusedVariables false in rfl", "  sorry", ""], "forbidden diagnostic suppression linter.unusedVariables", false),
      ("guard-panic", #["#guard_panic in", "#check R4MissingPANIC"] ++ setup ++ statement ++ proof, "forbidden diagnostic suppression #guard_panic", false)] do
    let name := "diagnostic-" ++ variant
    let root ← withClaims ctx goodRoot name body
    check ctx name positive root diagnostic

/-- Check declaration-owned warning exceptions through layout, namespace and local-option variations. -/
def warningCases (ctx : Context) (goodRoot nv : FilePath) : IO Unit := do
  let warning ← withClaims ctx goodRoot "warning" (setup ++ statement ++ #["set_option warningAsError false", "/-- Module-wide suppression around the hole. -/", "theorem StatementProof : Statement := by sorry", ""])
  check ctx "warning" false warning "warningAsError suppression"
  let localRoot ← withClaims ctx goodRoot "warning-local-layout" (setup ++ statement ++ #["section Reviewed",
    "set_option /- option -/ warningAsError /- value -/ false in -- local", "/-- Registered proof under a parsed local exception. -/",
    "theorem _root_.Fixture.StatementProof : Statement := by", "  set_option warningAsError false in", "    sorry", "end Reviewed", ""])
  check ctx "warning-local-layout" true localRoot
  for scope in #["file","section","namespace","split"] do
    let start := #["set_option warningAsError false -- trailing comment"]
    let head := if scope == "section" then #["section Quiet"] ++ start else if scope == "namespace" then #["namespace Quiet"] ++ start ++ #["end Quiet"]
      else if scope == "split" then #["set_option /- split -/ warningAsError", "  false -- trailing comment"] else start
    let tail := if scope == "section" then #["end Quiet"] else #[]
    let root ← withClaims ctx goodRoot ("warning-" ++ scope) (head ++ setup ++ statement ++ proof ++ tail)
    check ctx ("warning-" ++ scope) false root "unscoped warningAsError suppression"
  for (variant, body, source, diagnostic) in #[
      ("missing-exception", setup ++ statement ++ #["set_option warn.sorry false in", "/-- A quiet hole still requires its registered warning exception. -/", "theorem StatementProof : Statement := by sorry", ""], goodRoot, "unresolved proof needs exactly one declaration-local warningAsError exception"),
      ("borrowed-local", #["set_option warningAsError false -- file-wide exception", "set_option warningAsError false in"] ++ setup ++ statement ++ #["/-- Bound stub borrowing the setup declaration exception. -/", "theorem StatementProof : Statement := by sorry", ""], goodRoot, "unscoped warningAsError suppression"),
      ("unrelated-local", #["set_option warningAsError false in"] ++ setup ++ statement ++ proof, goodRoot, "unscoped warningAsError suppression"),
      ("term", #["/-- A setup value cannot disable warnings. -/", "def Setup : Prop := set_option warningAsError false in False", ""] ++ statement ++ proof, goodRoot, "unscoped warningAsError suppression"),
      ("completed", setup ++ statement ++ proof ++ #["set_option warningAsError false in"] ++ nonvacuity, nv, "warningAsError exception is not a registered unresolved proof"),
      ("tactic", setup ++ statement ++ proof ++ #["/-- A completed witness cannot disable warnings in its tactic. -/", "theorem StatementNonvacuity : Nonempty Statement := by", "  set_option warningAsError false in", "    exact ⟨fun h => h⟩", ""], nv, "unscoped warningAsError suppression")] do
    let root ← withClaims ctx source ("warning-" ++ variant) body
    check ctx ("warning-" ++ variant) false root diagnostic
  let matrix ← clone ctx goodRoot "warning-scoped-notation"
  writeModule matrix "Fixture/Claims.lean" #["Mathlib.Init","Mathlib.LinearAlgebra.Matrix.Defs"] (setup ++ #["open scoped Matrix",
    "/-- A source proposition using imported scoped notation. -/", "def Statement : Prop := Setup → ∀ M : Matrix Unit Unit Nat, Mᵀ = M", ""] ++ proof)
  add matrix "statement-imports.tsv" "Fixture.Claims\t2\tMathlib.LinearAlgebra.Matrix.Defs\ttrue\tfalse\tfalse"
  check ctx "warning-scoped-notation" true matrix
  let umbrella ← clone ctx goodRoot "warning-umbrella"
  let source ← IO.FS.readFile (umbrella / "Fixture/Skeleton.lean")
  write umbrella "Fixture/Skeleton.lean" (source ++ "set_option warningAsError false -- umbrella exception\n")
  check ctx "warning-umbrella" false umbrella "unscoped warningAsError suppression"

/-- Run only the ninety pure semantic cases against independent copies of the unmodified common fixture. -/
def run (ctx : Context) : IO Unit := do
  let passed ← ctx.accepted.get
  let rejected ← ctx.rejected.get
  let goodRoot ← good ctx
  let initial ← fingerprint ctx goodRoot
  let nv ← propositionCases ctx goodRoot
  frozenCases ctx goodRoot nv
  contextCases ctx goodRoot
  bindingCases ctx goodRoot
  vocabularyCases ctx goodRoot nv
  diagnosticCases ctx goodRoot
  warningCases ctx goodRoot nv
  ensure ((← fingerprint ctx goodRoot) == initial) "pure cases changed the shared GOOD registry"
  ensure ((← ctx.accepted.get) - passed == 17 && (← ctx.rejected.get) - rejected == 73)
    "skeleton pure matrix differs from 90 cases (17 positive, 73 negative)"
  IO.println "test-skeleton-pure: ok (90 cases; 17 positive, 73 negative)"

end Checker.Tests.SkeletonPure
