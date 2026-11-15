import Checker.Tests.Registry
import Checker.Tests.TreePolicy
import Checker.Tests.Vocabulary
import Checker.Tests.BaseDiff
import Checker.Tests.Multisource
import Checker.Tests.SkeletonPure
import Checker.Tests.SkeletonComposed
import Checker.Tests.Corrections
import Checker.Tests.Content
import Checker.Tests.Selector

/-! The sole regression group registry, with direct runners and explicit runtime reader closures. -/
namespace Checker.Regressions
open System Checker.TestSupport

/-- One independent input/acceptance unit; a successful unrelated group cannot cover it. -/
structure Group where
  name : String
  run : Context → IO Unit
  inputs : Array String
  corpus : Bool := false
  headers : Bool := false
  policy : Bool := false
  layout : Bool := false
  history : Bool := false
  production : Bool := false
  /-- External Mathlib fixture roots; generated fixture modules are deliberately excluded. -/
  mathlibImports : Array String := #[]

/-- Native data validation also reaches the existing standalone content contract. -/
def dataInputs : Array String := #["Checker/Data.lean","scripts/check-content-amendments.py"]

/-- Explicit transition callbacks read the full dedicated event and ordinary-history contracts. -/
def transitionInputs : Array String := dataInputs ++ #["Checker/BaseDiff.lean","Checker/Corrections.lean",
  "Checker/History.lean","Checker/Selector.lean","Checker/Transition.lean"]

/-- Shared semantic drivers read their real elaborators and effective Lake decoder. -/
def semanticInputs : Array String := #["Checker/SemanticDriver.lean","Checker/Semantic.lean","Checker/LakeIsolation.lean"]

/-- Every group uses this executable facade and the same non-optimizable process/fixture oracles. -/
def commonInputs : Array String := #["Checker/Main.lean","Checker/Regressions.lean","Checker/Support.lean","Checker/TestSupport.lean",
  "lean-toolchain","lake-manifest.json","lakefile.toml"]

/-- Leaf groups preserve the union of all former harness cases without replaying an unrelated wrapper. -/
def groups : Array Group := #[
  {name := "registry", run := fun ctx => Checker.Tests.Registry.run ctx,
    inputs := dataInputs ++ #["Checker/Tests/Fixtures.lean","Checker/Tests/Registry.lean"], corpus := true},
  {name := "tree-policy", run := Checker.Tests.TreePolicy.run,
    inputs := dataInputs ++ transitionInputs ++ semanticInputs ++ #["Checker/Tests/TreePolicy.lean","LatticeSystem.lean"], policy := true},
  {name := "vocabulary-registry", run := Checker.Tests.Vocabulary.registry,
    inputs := dataInputs ++ #["Checker/Tests/Fixtures.lean","Checker/Tests/Vocabulary.lean"], corpus := true},
  {name := "vocabulary-semantic", run := Checker.Tests.Vocabulary.semantic,
    inputs := semanticInputs ++ #["Checker/Vocabulary.lean","Checker/Tests/Fixtures.lean","Checker/Tests/Vocabulary.lean"], mathlibImports := #["Mathlib.Data.Nat.Basic"]},
  {name := "base-diff", run := Checker.Tests.BaseDiff.run,
    inputs := transitionInputs ++ #["Checker/Tests/Fixtures.lean","Checker/Tests/BaseDiff.lean"], corpus := true},
  {name := "multisource", run := Checker.Tests.Multisource.run,
    inputs := transitionInputs ++ #["Checker/Tests/Fixtures.lean","Checker/Tests/Multisource.lean"]},
  {name := "skeleton-pure", run := Checker.Tests.SkeletonPure.run,
    inputs := semanticInputs ++ #["Checker/Skeleton.lean","Checker/Tests/Fixtures.lean","Checker/Tests/SkeletonFixture.lean","Checker/Tests/SkeletonPure.lean"], mathlibImports := #["Mathlib.Init","Mathlib.LinearAlgebra.Matrix.Defs"]},
  {name := "skeleton-composed", run := Checker.Tests.SkeletonComposed.run,
    inputs := dataInputs ++ semanticInputs ++ #["Checker/Skeleton.lean","Checker/Vocabulary.lean","Checker/Tests/Fixtures.lean",
      "Checker/Tests/FixtureSupport.lean","Checker/Tests/SkeletonFixture.lean","Checker/Tests/SkeletonComposed.lean",
      "scripts/generate-public-docs.py","LatticeSystem.lean",".gitignore"], headers := true, policy := true, layout := true, mathlibImports := #["Mathlib.Init"]},
  {name := "corrections", run := Checker.Tests.Corrections.run,
    inputs := transitionInputs ++ semanticInputs ++ #["Checker/Vocabulary.lean","Checker/Tests/FixtureSupport.lean","Checker/Tests/Corrections.lean","scripts/generate-public-docs.py"], corpus := true, history := true, production := true},
  {name := "content", run := Checker.Tests.Content.run,
    inputs := transitionInputs ++ #["Checker/Tests/FixtureSupport.lean","Checker/Tests/Content.lean","scripts/generate-public-docs.py"], corpus := true, history := true},
  {name := "selector", run := Checker.Tests.Selector.run,
    inputs := #["Checker/History.lean","Checker/Selector.lean","Checker/Tests/Fixtures.lean","Checker/Tests/Selector.lean"]}]

/-- Run exactly one named leaf in its own automatically retired external fixture context. -/
def run (project executable : FilePath) (name : String) : IO Unit := do
  let some group := groups.find? (·.name == name) | throw <| IO.userError s!"unknown regression group: {name}"
  withContext project executable group.run

end Checker.Regressions
