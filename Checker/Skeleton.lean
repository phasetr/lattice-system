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
Decide whether a proposition is already discharged by the hypotheses gathered
so far. `True`, a repeated hypothesis, a conjunction of such components, and an
implication whose own antecedent supplies the conclusion all qualify. Each step
reduces one head, so a wrapper definition cannot hide the shape; `fuel` bounds
that unfolding.
-/
private meta partial def impliedByHypotheses (hypotheses : Array Expr) (fuel : Nat)
    (conclusion : Expr) : MetaM Bool := do
  if hypotheses.any (· == conclusion) then return true
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    let reduced ← Meta.whnf conclusion
    if hypotheses.any (· == reduced) then return true
    if reduced.isConstOf (Name.mkSimple "True") then return true
    if reduced.isAppOfArity (Name.mkSimple "And") 2 then
      let left ← impliedByHypotheses hypotheses fuel reduced.appFn!.appArg!
      return left && (← impliedByHypotheses hypotheses fuel reduced.appArg!)
    if reduced.isForall then
      let nested ← Meta.forallBoundedTelescope reduced (some 1) fun binders body => do
        let mut extended := hypotheses
        for binder in binders do extended := extended.push (← Meta.inferType binder)
        impliedByHypotheses extended fuel body
      return nested
    return false

/--
Report whether a declaration type is a self-fulfilling obligation. The first
component holds when its conclusion reduces to `True`; the second holds when the
whole obligation follows from its own hypotheses, which covers `(h : P) : P`,
`(h : P) : P ∧ True`, and the same shapes wrapped in a definition. Both are
rejected as nonvacuity evidence.
-/
private meta def selfFulfillingFacts (type : Expr) : MetaM (Bool × Bool) := do
  let concludesTrue ← Meta.forallTelescope type fun _ conclusion => do
    return (← Meta.whnf conclusion).isConstOf (Name.mkSimple "True")
  return (concludesTrue, ← impliedByHypotheses #[] 16 type)

/--
Name the declaration type when it is exactly a universe-monomorphic constant.
A registered proof obligation is spelled as its bound primary statement, so any
larger type reports `NONE` and cannot match a binding.
-/
private meta def typeConstantName (info : ConstantInfo) : String :=
  match info.type.consumeMData with
  | .const name levels => if levels.isEmpty then toString name else "NONE"
  | _ => "NONE"

/-- Recognize the parsed option command, term, or tactic, independent of layout. -/
private meta def disablesWarnings (stx : Syntax) : Bool :=
  (stx.isOfKind ``Parser.Command.set_option ||
    stx.isOfKind ``Parser.Term.set_option ||
    stx.isOfKind ``Parser.Tactic.set_option) &&
  stx[1].isIdent && stx[1].getId == `warningAsError && stx[3].getAtomVal == "false"

/--
Report warning exceptions from parsed commands. Only an immediate theorem
declaration can own a command-level exception. Its actual imported declaration
range, rather than a guessed namespace spelling, determines its identity.
Nested term/tactic options stay inside that same declaration's exception.
-/
private meta partial def warningLines (moduleName : Name) (fileMap : FileMap)
    (theorems : Array (Name × Position)) (stx : Syntax)
    (insideException := false) : Array String := Id.run do
  let line (owner scope : String) :=
    String.intercalate "\t" ["W", toString moduleName, owner, scope]
  if stx.isOfKind ``Parser.Command.in && disablesWarnings stx[0] then
    let declaration := stx[2]
    let theoremSyntax := declaration[1]
    let owner := if declaration.isOfKind ``Parser.Command.declaration &&
        theoremSyntax.isOfKind ``Parser.Command.theorem then
      theoremSyntax[1][0].getPos? >>= fun pos =>
        (theorems.find? fun entry => entry.2 == fileMap.toPosition pos).map (·.1)
      else none
    return #[line (owner.map toString |>.getD "NONE") "declaration"] ++
      warningLines moduleName fileMap theorems declaration owner.isSome
  if disablesWarnings stx && !insideException then
    return #[line "NONE" "unscoped"]
  let mut result := #[]
  for child in stx.getArgs do
    result := result ++ warningLines moduleName fileMap theorems child insideException
  return result

/-- Parse each registered module using Lean's parser and exact declaration ranges. -/
private meta def moduleWarningLines (env : Environment) (moduleName : Name)
    (sourcePath : System.FilePath) : CommandElabM (Array String) := do
  let some idx := moduleIndex? env moduleName
    | throwError "warning scope module {moduleName} is absent"
  let mut theorems := #[]
  for info in env.header.moduleData[idx]!.constants do
    if let .thmInfo _ := info then
      let some ranges ← findDeclarationRanges? info.name
        | continue  -- A wrapper without a matching range is never permitted.
      theorems := theorems.push (info.name, ranges.selectionRange.pos)
  let contents ← IO.FS.readFile sourcePath
  let inputCtx := Parser.mkInputContext contents sourcePath.toString
  -- The parser rejects recovery/errors; comments and line breaks are syntax,
  -- not a second, incomplete shell lexer for Lean commands.
  let parsed ← Parser.testParseFile env sourcePath
  return warningLines moduleName inputCtx.fileMap theorems parsed.raw

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
  let (concludesTrue, selfFulfilling) ← selfFulfillingFacts info.type
  return String.intercalate "\t" [
    "D", toString moduleName, toString info.name, declarationKind env info,
    boolField isProp, toString (directSorryCount info),
    boolField (axioms.contains (Name.mkSimple "sorryAx")),
    namesField (typeConstants info), namesField (valueConstants info),
    namesField axioms, namesField (binderDomainConstants info.type),
    namesField (value.map binderDomainConstants |>.getD #[]),
    boolField isTrueValue, boolField (isPropValue.getD false),
    boolField concludesTrue, boolField selfFulfilling, typeConstantName info,
    encodeExpr info.levelParams info.type, valueEncoding info]

/-- Inspect all registered statement modules in one elaborated environment. -/
private meta def dumpEnvironment (moduleListPath outputPath rootPath registryPath : String) :
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
  for row in (← IO.FS.readFile registryPath).splitOn "\n" |>.drop 1 do
    let fields := row.splitOn "\t" |>.toArray
    if fields.size == 3 then
      lines := lines ++ (← moduleWarningLines env fields[0]!.toName
        (System.FilePath.mk rootPath / fields[1]!))
  let body := String.intercalate "\n" lines.toList
  IO.FS.writeFile outputPath (if body.isEmpty then body else body ++ "\n")

syntax "#skeleton_dump " str str str str : command

elab_rules : command
  | `(#skeleton_dump $moduleList:str $output:str $root:str $registry:str) =>
      dumpEnvironment moduleList.getString output.getString root.getString registry.getString

end

end SkeletonChecker
