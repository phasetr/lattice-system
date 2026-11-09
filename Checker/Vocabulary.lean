module

public meta import Checker.Semantic

/-!
Vocabulary environment dumper.

This checker deliberately reports kernel/environment facts instead of trying to
recover declarations or imports from source text. The shell driver compares the
resulting facts with the three vocabulary registry tables.
-/

open Lean Elab Command
open SemanticChecker

namespace VocabularyChecker

/--
Exact Lean 4.29 structure implementation artifacts that are not independently
registerable vocabulary. Constructors, recursors, and projections are not in
this list and therefore remain mandatory generated vocabulary rows.
-/
private meta def isStructureImplementationArtifact
    (structures : Array Name) (declName : Name) : Bool :=
  let name := toString declName
  structures.any fun structureName =>
    let base := toString structureName
    ["._sizeOf_1", "._sizeOf_inst", ".casesOn", ".ctorIdx", ".mk._flat_ctor",
      ".mk.inj", ".mk.injEq", ".mk.noConfusion", ".mk.sizeOf_spec",
      ".noConfusion", ".noConfusionType", ".recOn"].any fun suffix =>
        name == base ++ suffix

/-- Inspect registered modules and write declaration/import facts for the shell driver. -/
private meta def dumpEnvironment (moduleListPath outputPath : String) : CommandElabM Unit := do
  let moduleText ← IO.FS.readFile moduleListPath
  let moduleNames := parseModuleList moduleText
  let env ← getEnv
  let mut lines := #[]
  for moduleName in moduleNames do
    let some idx := moduleIndex? env moduleName
      | throwError "registered module {moduleName} is absent from the elaborated environment"
    let data := env.header.moduleData[idx]!
    let structures := data.constants.filterMap fun
      | .inductInfo v => if isStructure env v.name then some v.name else none
      | _ => none
    for info in data.constants do
      unless isStructureImplementationArtifact structures info.name do
        lines := lines.push (← liftTermElabM <|
          vocabularyDeclarationLine env moduleName info)
    for h : i in *...data.imports.size do
      lines := lines.push (importLine moduleName (i + 1) data.imports[i])
  let body := String.intercalate "\n" lines.toList
  IO.FS.writeFile outputPath (if body.isEmpty then body else body ++ "\n")

syntax "#vocabulary_dump " str str : command

elab_rules : command
  | `(#vocabulary_dump $moduleList:str $output:str) =>
      dumpEnvironment moduleList.getString output.getString

end VocabularyChecker
