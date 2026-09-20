module

public meta import Lean
public meta import Lean.Environment
public meta import Lean.Meta.Instances
public meta import Lean.ProjFns

/-!
Shared, version-pinned semantic encodings for the registry environment
checkers. Moving these definitions out of an individual phase checker keeps
the R3 vocabulary dump and its Git object identifiers byte-for-byte stable.
-/

open Lean

namespace SemanticChecker

@[expose] public section

/-- Encode a name without relying on pretty-printer configuration. -/
meta def encodeName : Name → String
  | .anonymous => "n"
  | .str p s =>
      let parent := encodeName p
      s!"s{parent.length}:{parent}:{s.length}:{s}"
  | .num p n =>
      let parent := encodeName p
      s!"i{parent.length}:{parent}:{n}"

/-- Encode a universe level, alpha-normalizing declaration universe parameters. -/
meta partial def encodeLevel (params : List Name) : Level → String
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
meta def encodeBinderInfo : BinderInfo → String
  | .default => "e"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Encode literals without introducing control characters into a TSV dump. -/
meta def encodeLiteral : Literal → String
  | .natVal n => s!"n{n}"
  | .strVal s =>
      let codes := s.toList.map (fun c => toString c.toNat)
      s!"s{codes.length}:{String.intercalate "," codes}"

/-- Canonical structural expression serialization for Git object hashing. -/
meta partial def encodeExpr (params : List Name) : Expr → String
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
meta def declarationKind (env : Environment) (info : ConstantInfo) : String :=
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
meta def generatedParent? (env : Environment) : ConstantInfo → Option Name
  | .ctorInfo v => some v.induct
  | .recInfo v => v.all.head?
  | .defnInfo v => env.getProjectionStructureName? v.name
  | _ => none

/-- Collect constants occurring directly in a declaration's type and value. -/
meta def directConstants : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants

/-- Collect constants in the declaration type only. -/
meta def typeConstants (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants

/-- Collect constants in a definition or theorem value when one exists. -/
meta def valueConstants : ConstantInfo → Array Name
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

/-- Canonical value encoding for declarations that carry a kernel value. -/
meta def valueEncoding : ConstantInfo → String
  | .defnInfo v => encodeExpr v.levelParams v.value
  | .thmInfo v => encodeExpr v.levelParams v.value
  | .opaqueInfo v => encodeExpr v.levelParams v.value
  | _ => "NONE"

/-- Return the kernel value when the declaration carries one. -/
meta def valueExpr? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/--
Collect constants used in binder domains of an expression. For propositions,
this records constants used as explicit antecedents or dependent hypotheses.
-/
meta partial def binderDomainConstants : Expr → Array Name
  | .forallE _ domain body _ =>
      domain.getUsedConstants ++ binderDomainConstants body
  | .lam _ domain body _ =>
      domain.getUsedConstants ++ binderDomainConstants body
  | .letE _ type value body _ =>
      type.getUsedConstants ++ value.getUsedConstants ++ binderDomainConstants body
  | .mdata _ expr => binderDomainConstants expr
  | _ => #[]

/-- Count literal occurrences of a kernel constant in an expression. -/
meta partial def countConstant (wanted : Name) : Expr → Nat
  | .const name _ => if name == wanted then 1 else 0
  | .app f a => countConstant wanted f + countConstant wanted a
  | .lam _ d b _ => countConstant wanted d + countConstant wanted b
  | .forallE _ d b _ => countConstant wanted d + countConstant wanted b
  | .letE _ t v b _ =>
      countConstant wanted t + countConstant wanted v + countConstant wanted b
  | .mdata _ e => countConstant wanted e
  | .proj _ _ e => countConstant wanted e
  | _ => 0

/-- Count direct sorryAx occurrences in the declaration value. -/
meta def directSorryCount : ConstantInfo → Nat
  | .defnInfo v => countConstant (Name.mkSimple "sorryAx") v.value
  | .thmInfo v => countConstant (Name.mkSimple "sorryAx") v.value
  | .opaqueInfo v => countConstant (Name.mkSimple "sorryAx") v.value
  | _ => 0

/-- Canonical semantic declaration payload separate from the declaration type. -/
meta def declarationPayload (env : Environment) (info : ConstantInfo) : String :=
  let kind := declarationKind env info
  match info with
  | .defnInfo v => s!"{kind}({encodeExpr v.levelParams v.value})"
  | .thmInfo v => s!"{kind}({encodeExpr v.levelParams v.value})"
  | .opaqueInfo v => s!"{kind}({encodeExpr v.levelParams v.value})"
  | _ =>
      let parent := (generatedParent? env info).map encodeName |>.getD "NONE"
      s!"{kind}({parent})"

/-- Render a Boolean in the spelling used by registry schemas. -/
meta def boolField (b : Bool) : String := if b then "true" else "false"

/-- Test whether a type directly mentions a named kernel constant. -/
meta def typeUses (constantName : String) (info : ConstantInfo) : Bool :=
  info.type.getUsedConstants.any fun name => toString name == constantName

/-- Render the unchanged R3 vocabulary declaration record. -/
meta def vocabularyDeclarationLine (env : Environment) (moduleName : Name)
    (info : ConstantInfo) : MetaM String := do
  let directSorry := (directConstants info).contains (Name.mkSimple "sorryAx")
  let axioms ← Lean.collectAxioms info.name
  let transitiveSorry := axioms.contains (Name.mkSimple "sorryAx")
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

/-- Render one direct module import, preserving its environment flags. -/
meta def importLine (moduleName : Name) (position : Nat) (imp : Import) : String :=
  String.intercalate "\t" [
    "I", toString moduleName, toString position, toString imp.module,
    boolField imp.isExported, boolField imp.isMeta, boolField imp.importAll]

/-- Parse a newline-delimited module list supplied by a shell driver. -/
meta def parseModuleList (contents : String) : Array Name :=
  (contents.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii
    if line.isEmpty then none else some line.toName).toArray

/-- Locate imported module data by its semantic module name. -/
meta def moduleIndex? (env : Environment) (moduleName : Name) : Option Nat :=
  env.header.moduleNames.findIdx? (fun n => n == moduleName)

end

end SemanticChecker
