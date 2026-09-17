module

public meta import Lean
public meta import Lean.Environment
public meta import Lean.Meta.Instances
public meta import Lean.ProjFns

/-!
R3 vocabulary environment dumper.

This checker deliberately reports kernel/environment facts instead of trying to
recover declarations or imports from source text.  `scripts/check-vocabulary.sh`
compares the resulting facts with the three R3 registry tables.
-/

open Lean Elab Command

namespace R3Vocabulary

/-- Encode a name without relying on pretty-printer configuration. -/
private meta def encodeName : Name → String
  | .anonymous => "n"
  | .str p s =>
      let parent := encodeName p
      s!"s{parent.length}:{parent}:{s.length}:{s}"
  | .num p n =>
      let parent := encodeName p
      s!"i{parent.length}:{parent}:{n}"

/-- Encode a universe level, alpha-normalizing declaration universe parameters. -/
private meta partial def encodeLevel (params : List Name) : Level → String
  | .zero => "z"
  | .succ u => s!"s({encodeLevel params u})"
  | .max u v => s!"m({encodeLevel params u},{encodeLevel params v})"
  | .imax u v => s!"i({encodeLevel params u},{encodeLevel params v})"
  | .param n =>
      match params.idxOf? n with
      | some i => s!"p{i}"
      | none => s!"x({encodeName n})"
  | .mvar n => s!"?({encodeName n.name})"

/-- Encode the four kernel binder annotations. -/
private meta def encodeBinderInfo : BinderInfo → String
  | .default => "e"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Encode literals without introducing control characters into the TSV dump. -/
private meta def encodeLiteral : Literal → String
  | .natVal n => s!"n{n}"
  | .strVal s =>
      let codes := s.toList.map (fun c => toString c.toNat)
      s!"s{codes.length}:{String.intercalate "," codes}"

/--
Canonical structural declaration-type serialization used as the input to
`git hash-object --stdin`.  Binder names and metadata are intentionally erased;
de Bruijn indices and binder annotations retain the semantic binding shape.
-/
private meta partial def encodeExpr (params : List Name) : Expr → String
  | .bvar i => s!"b{i}"
  | .fvar n => s!"f({encodeName n.name})"
  | .mvar n => s!"?({encodeName n.name})"
  | .sort u => s!"s({encodeLevel params u})"
  | .const n us =>
      let levels := us.map (encodeLevel params)
      s!"c({encodeName n};{String.intercalate "," levels})"
  | .app f a => s!"a({encodeExpr params f},{encodeExpr params a})"
  | .lam _ d b bi =>
      s!"l{encodeBinderInfo bi}({encodeExpr params d},{encodeExpr params b})"
  | .forallE _ d b bi =>
      s!"p{encodeBinderInfo bi}({encodeExpr params d},{encodeExpr params b})"
  | .letE _ t v b _ =>
      s!"e({encodeExpr params t},{encodeExpr params v},{encodeExpr params b})"
  | .lit l => s!"v({encodeLiteral l})"
  | .mdata _ e => encodeExpr params e
  | .proj n i e => s!"r({encodeName n},{i},{encodeExpr params e})"

/-- Classify a constant using semantic environment extensions where necessary. -/
private meta def declarationKind (env : Environment) (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo v =>
      if isClass env v.name then "class"
      else if isStructure env v.name then "structure"
      else "inductive"
  | .defnInfo v =>
      if env.isProjectionFn v.name then "projection"
      else if Meta.isInstanceCore env v.name then "instance"
      else if v.hints.isAbbrev then "abbrev"
      else "definition"

/-- Return the inductive or structure that generated a surface declaration. -/
private meta def generatedParent? (env : Environment) : ConstantInfo → Option Name
  | .ctorInfo v => some v.induct
  | .recInfo v => v.all.head?
  | .defnInfo v => env.getProjectionStructureName? v.name
  | _ => none

/-- Collect constants occurring directly in a declaration's type and value. -/
private meta def directConstants : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants

/--
Canonical semantic payload separate from the declaration type.  Definitions,
abbreviations, theorems, and opaque declarations include their kernel value,
so a body/RHS change cannot hide behind an unchanged type.  Declarations with
no kernel value bind their kind and generated-parent identity here; their type
is hashed independently.
-/
private meta def declarationPayload (env : Environment) (info : ConstantInfo) : String :=
  let kind := declarationKind env info
  match info with
  | .defnInfo v => s!"{kind}({encodeExpr v.levelParams v.value})"
  | .thmInfo v => s!"{kind}({encodeExpr v.levelParams v.value})"
  | .opaqueInfo v => s!"{kind}({encodeExpr v.levelParams v.value})"
  | _ =>
      let parent := (generatedParent? env info).map encodeName |>.getD "NONE"
      s!"{kind}({parent})"

/-- Render a Boolean in the spelling used by the registry schema. -/
private meta def boolField (b : Bool) : String := if b then "true" else "false"

/-- Test whether a type directly mentions a named kernel constant. -/
private meta def typeUses (constantName : String) (info : ConstantInfo) : Bool :=
  info.type.getUsedConstants.any fun name => toString name == constantName

/-- Render all semantic facts for one owned declaration. -/
private meta def declarationLine (env : Environment) (moduleName : Name)
    (info : ConstantInfo) : MetaM String := do
  let directSorry := (directConstants info).contains ``sorryAx
  let axioms ← Lean.collectAxioms info.name
  let transitiveSorry := axioms.contains ``sorryAx
  let isProp ← Meta.isProp info.type
  let parent := (generatedParent? env info).map toString |>.getD "NONE"
  return String.intercalate "\t" [
    "D", toString moduleName, toString info.name,
    declarationKind env info, parent, boolField isProp,
    boolField directSorry, boolField transitiveSorry,
    boolField (typeUses "SimpleGraph" info),
    boolField (typeUses "Fintype" info),
    boolField (typeUses "Finset" info),
    encodeExpr info.levelParams info.type, declarationPayload env info]

/-- Render one direct module import, preserving its environment position and flags. -/
private meta def importLine (moduleName : Name) (position : Nat) (imp : Import) : String :=
  String.intercalate "\t" [
    "I", toString moduleName, toString position, toString imp.module,
    boolField imp.isExported, boolField imp.isMeta, boolField imp.importAll]

/-- Parse the newline-delimited registered module list supplied by the shell driver. -/
private meta def parseModuleList (contents : String) : Array Name :=
  (contents.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii
    if line.isEmpty then none else some line.toName).toArray

/-- Locate imported module data by its semantic module name. -/
private meta def moduleIndex? (env : Environment) (moduleName : Name) : Option Nat :=
  env.header.moduleNames.findIdx? (fun n => n == moduleName)

/--
Exact Lean 4.29 structure implementation artifacts that are not independently
registerable vocabulary.  Constructors, recursors, and projections are not in
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
      | throwError "registered module `{moduleName}` is absent from the elaborated environment"
    let data := env.header.moduleData[idx]!
    let structures := data.constants.filterMap fun
      | .inductInfo v => if isStructure env v.name then some v.name else none
      | _ => none
    for info in data.constants do
      unless isStructureImplementationArtifact structures info.name do
        lines := lines.push (← liftTermElabM <| declarationLine env moduleName info)
    for h : i in *...data.imports.size do
      lines := lines.push (importLine moduleName (i + 1) data.imports[i])
  let body := String.intercalate "\n" lines.toList
  IO.FS.writeFile outputPath (if body.isEmpty then body else body ++ "\n")

syntax "#r3_vocabulary_dump " str str : command

elab_rules : command
  | `(#r3_vocabulary_dump $moduleList:str $output:str) =>
      dumpEnvironment moduleList.getString output.getString

end R3Vocabulary
