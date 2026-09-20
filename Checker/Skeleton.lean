module

public meta import Checker.Semantic

/-!
Typed-skeleton environment dumper.

The shell driver supplies the exact statement-module list and compares this
semantic output with bindings, imports, dependencies, contexts, and axioms.
-/

open Lean Elab Command
open SemanticChecker

namespace SkeletonChecker

@[expose] public section

/-- Render names as a comma-separated field for the shell-side set checks. -/
private meta def namesField (names : Array Name) : String :=
  String.intercalate "," (names.toList.map toString)

/--
Report whether a declaration type is a self-fulfilling obligation. The first
component holds when its conclusion reduces to `True`; the second holds when
the conclusion repeats one of the declaration's own hypotheses, the `(h : P) : P`
shape. Both are rejected as nonvacuity evidence.
-/
private meta def selfFulfillingFacts (type : Expr) : MetaM (Bool × Bool) :=
  Meta.forallTelescope type fun binders conclusion => do
    let concludesTrue := (← Meta.whnf conclusion).isConstOf (Name.mkSimple "True")
    let mut repeatsHypothesis := false
    for binder in binders do
      if (← Meta.inferType binder) == conclusion then repeatsHypothesis := true
    return (concludesTrue, repeatsHypothesis)

/-- Render semantic facts for one declaration owned by a statement module. -/
private meta def declarationLine (env : Environment) (moduleName : Name)
    (info : ConstantInfo) : MetaM String := do
  let axioms ← Lean.collectAxioms info.name
  let isProp ← Meta.isProp info.type
  let value := valueExpr? info
  let reducedValue ← value.mapM Meta.whnf
  let isTrueValue := reducedValue.any fun
    | .const name _ => name == Name.mkSimple "True"
    | _ => false
  -- A primary statement carries its proposition as a value, so its own type is
  -- `Prop` and `Meta.isProp` on that type is necessarily false.
  let isPropValue ← value.mapM Meta.isProp
  let (concludesTrue, repeatsHypothesis) ← selfFulfillingFacts info.type
  return String.intercalate "\t" [
    "D", toString moduleName, toString info.name, declarationKind env info,
    boolField isProp, toString (directSorryCount info),
    boolField (axioms.contains (Name.mkSimple "sorryAx")),
    namesField (typeConstants info), namesField (valueConstants info),
    namesField axioms, namesField (value.map binderDomainConstants |>.getD #[]),
    boolField isTrueValue, boolField (isPropValue.getD false),
    boolField concludesTrue, boolField repeatsHypothesis,
    encodeExpr info.levelParams info.type, valueEncoding info]

/-- Inspect all registered statement modules in one elaborated environment. -/
private meta def dumpEnvironment (moduleListPath outputPath : String) :
    CommandElabM Unit := do
  let moduleNames := parseModuleList (← IO.FS.readFile moduleListPath)
  let env ← getEnv
  let mut lines := #[]
  for moduleName in moduleNames do
    let some idx := moduleIndex? env moduleName
      | throwError "registered statement module {moduleName} is absent"
    let data := env.header.moduleData[idx]!
    for info in data.constants do
      lines := lines.push (← liftTermElabM <| declarationLine env moduleName info)
    for h : i in *...data.imports.size do
      lines := lines.push (importLine moduleName (i + 1) data.imports[i])
  let body := String.intercalate "\n" lines.toList
  IO.FS.writeFile outputPath (if body.isEmpty then body else body ++ "\n")

syntax "#skeleton_dump " str str : command

elab_rules : command
  | `(#skeleton_dump $moduleList:str $output:str) =>
      dumpEnvironment moduleList.getString output.getString

end

end SkeletonChecker
