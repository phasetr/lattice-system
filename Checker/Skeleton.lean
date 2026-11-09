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
    for hypothesis in hypotheses do
      if (← Meta.whnf hypothesis) == reduced then return true
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
rejected as nonvacuity evidence. `.all` also opens irreducible definitions;
this local classification does not change the expression encodings.
-/
private meta def selfFulfillingFacts (type : Expr) : MetaM (Bool × Bool) :=
  Meta.withTransparency .all do
    let concludesTrue ← Meta.forallTelescope type fun _ conclusion => do
      return (← Meta.whnf conclusion).isConstOf (Name.mkSimple "True")
    return (concludesTrue, ← impliedByHypotheses #[] 16 type)

/--
Name an exact primary type at the proof declaration's own ordered universe
parameters. The primary and proof must quantify the same number of universes;
specialized, reordered, duplicated, or extra levels report `NONE`, as do larger
types. Parameter names may differ between the two declarations.
-/
private meta def typeConstantName (env : Environment) (info : ConstantInfo) : String :=
  match info.type.consumeMData with
  | .const name levels =>
    match env.find? name with
    | some target =>
      if target.levelParams.length == info.levelParams.length &&
          levels == info.levelParams.map Level.param then toString name else "NONE"
    | none => "NONE"
  | _ => "NONE"

/-- The four direct option syntaxes handled by the pinned Lean elaborators. -/
private meta def isSetOptionSyntax (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.set_option ||
  stx.isOfKind ``Parser.Term.set_option ||
  stx.isOfKind ``Parser.Tactic.set_option ||
  stx.isOfKind `Lean.Parser.Tactic.Grind.setOption

/-- Recognize the parsed option command, term, or tactic, independent of layout. -/
private meta def disablesWarnings (stx : Syntax) : Bool :=
  isSetOptionSyntax stx &&
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

/--
Record direct mechanisms that consume diagnostics or disable a diagnostic
checker. These events are distinct from the one owned warningAsError exception;
no such additional exemption is permitted inside an owned proof either.
-/
private meta partial def suppressionLines (moduleName : Name) (stx : Syntax) :
    Array String := Id.run do
  let mut result := #[]
  let line (mechanism : String) :=
    String.intercalate "\t" ["S", toString moduleName, mechanism]
  -- The pinned runAndCollectMessages API has exactly these two direct handlers.
  for (kind, spelling) in #[(`Lean.guardMsgsCmd, "#guard_msgs"),
      (`Lean.guardPanicCmd, "#guard_panic")] do
    if stx.isOfKind kind then result := result.push (line spelling)
  if stx.isOfKind `Batteries.Tactic.Lint.nolint then
    result := result.push (line "nolint")
  if isSetOptionSyntax stx &&
      stx[1].isIdent && stx[3].getAtomVal == "false" then
    let name := stx[1].getId.eraseMacroScopes
    if name.getRoot == `linter || name.getRoot == `warn then
      result := result.push (line (toString name))
  for child in stx.getArgs do
    result := result ++ suppressionLines moduleName child
  return result

/--
Recover command syntax through Lean's real frontend. Parsing and elaboration
advance together, so scoped notation, local syntax, and namespaces use the same
state as the source compilation rather than a fixed imported parser environment.
-/
private meta partial def sourceCommands (moduleName : Name)
    (inputCtx : Parser.InputContext) : IO (Array Syntax) := do
  let opts := Elab.async.set (({} : Options).setBool `warningAsError true) true
  let snap ← Language.Lean.process (fun header => pure <| .ok {
      mainModuleName := moduleName
      isModule := header.isModule
      imports := header.imports
      opts }) none { inputCtx with }
  if ← Language.toSnapshotTree snap |>.runAndReport opts false {} then
    throw <| IO.userError "failed to elaborate warning-scope source"
  let some processed := snap.processedResult.get
    | throw <| IO.userError "warning-scope source has no processed header"
  let mut current := processed.firstCmdSnap.get
  let mut commands := #[]
  repeat
    commands := commands.push current.stx
    let some next := current.nextCmdSnap? | break
    current := next.get
  return commands

/-- Inspect each registered module's frontend syntax and exact declaration ranges. -/
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
  let commands ← sourceCommands moduleName inputCtx
  return commands.flatMap fun command =>
    warningLines moduleName inputCtx.fileMap theorems command ++
      suppressionLines moduleName command

/-- Render semantic facts for one declaration owned by a statement module. -/
private meta def declarationLine (env : Environment) (moduleName : Name)
    (info : ConstantInfo) : MetaM String := do
  let axioms ← Lean.collectAxioms info.name
  let isProp ← Meta.isProp info.type
  let value := valueExpr? info
  let reducedValue ← Meta.withTransparency .all <| value.mapM Meta.whnf
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
    boolField concludesTrue, boolField selfFulfilling, typeConstantName env info,
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
