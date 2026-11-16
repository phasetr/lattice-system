import Checker.Corrections
import Checker.Selector

/-! Actual Git-base selection and directory fixture routes for permanent registry transitions. -/
namespace Checker.Transition
open Lean System Checker.CheckAll Checker.CheckAll.Registry Checker.History Checker.Selector

/-- A fixture base and current target are separately resolved under one owned external root. -/
def fixtureRoots (project : FilePath) (base target : String) : IO (FilePath × FilePath) := do
  let some owner ← IO.getEnv "LATTICE_TEST_ROOT" | throw <| IO.userError "fixture mode requires LATTICE_TEST_ROOT"
  let owner ← IO.FS.realPath owner
  let project ← IO.FS.realPath project
  let base ← IO.FS.realPath base; let target ← IO.FS.realPath target
  require (!pathWithin owner.toString project.toString)
    "LATTICE_TEST_ROOT must be repository-external"
  require (owner.toString != "/" && !pathWithin project.toString owner.toString) "LATTICE_TEST_ROOT must not contain the repository"
  require (pathWithin base.toString owner.toString) "fixture base must be below LATTICE_TEST_ROOT"
  require (pathWithin target.toString owner.toString) "fixture current must be below LATTICE_TEST_ROOT"
  require (base != project && target != project) "production root cannot use fixture mode"
  return (base,target)




/-- Ordinary history comparison delegates only a genuinely new event to the correction validator. -/
def baseDirectories (project base target : FilePath) (event : String := "")
    (allowSupersession : Bool := false) (directoryMode : Bool := true)
    (actualCommit : Option String := none) : IO Unit := do
  let old ← Checker.BaseDiff.snapshot base
  let current ← Checker.BaseDiff.snapshot target (← Checker.RegistryIO.currentProfile project target)
  let replay := !event.isEmpty && !(Checker.Corrections.rows old "correction-events").any (col · 1 == event)
  if replay then Checker.Corrections.validate project base target event actualCommit
  Checker.BaseDiff.validate {old with normalizeLines := directoryMode} current (allowSupersession || replay) replay event
  IO.println "check-base-diff: ok"

/-- Parsed ordinary base-comparison options retain their original argument-vector contract. -/
structure BaseOptions where
  event : String := ""
  supersession : Bool := false
  rest : List String := []

/-- Parse only the recognized leading options, without shell evaluation. -/
def parseBase (args : List String) : Except String BaseOptions :=
  let rec loop (args : List String) (options : BaseOptions) : Except String BaseOptions :=
    match args with
    | "--allow-supersession" :: rest => loop rest {options with supersession := true}
    | "--correction-event" :: event :: rest => loop rest {options with event}
    | ["--correction-event"] => .error "--correction-event requires an event ID"
    | "--fixture-dirs" :: _ => .ok {options with rest := args}
    | argument :: _ => if argument.startsWith "--" then .error s!"unknown option: {argument}"
      else .ok {options with rest := args}
    | [] => .ok options
  loop args {}

/-- A standalone ordinary history gate, including the explicit bootstrap-ancestor exception. -/
def baseEntry (project : FilePath) (args : List String) : IO Unit := do
  try
    let options ← IO.ofExcept (parseBase args)
    match options.rest with
    | ["--fixture-dirs",base,target] =>
      let (base,target) ← fixtureRoots project base target
      baseDirectories project base target options.event options.supersession
    | "--fixture-dirs" :: _ => throw <| IO.userError "usage: base-diff --fixture-dirs BASE CURRENT"
    | positional =>
      let (root,baseRef) ← match positional with
        | [] => pure (project,"HEAD^")
        | [root] => pure (FilePath.mk root,"HEAD^")
        | [root,baseRef] => pure (FilePath.mk root,baseRef)
        | _ => throw <| IO.userError "invalid base-diff arguments"
      let (root,base) ← actualBase root baseRef
      if !(← hasPath root base "registry/claims.tsv") then
        IO.println "check-base-diff: bootstrap skip (verified ancestor has no registry/claims.tsv)"
        return
      IO.FS.withTempDir fun temporary => do
        materialize root base temporary
        baseDirectories project temporary root options.event options.supersession false (some base)
  catch error => throw <| IO.userError s!"check-base-diff: {error}"

/-- Dedicated correction entry cannot manufacture an event or use an unverified historical base. -/
def correctionEntry (project : FilePath) (args : List String) : IO Unit := do
  try
    match args with
    | ["--fixture-dirs",base,target] =>
      let (base,target) ← fixtureRoots project base target
      Checker.Corrections.validate project base target
    | ["--correction-event",event,target,base] =>
      let root ← IO.FS.realPath target
      require (trim (← git root #["rev-parse","--show-toplevel"]) == root.toString) "ROOT must be the repository top"
      require (← hasPath root base "registry/claims.tsv") "base commit lacks the claim registry"
      IO.FS.withTempDir fun temporary => do
        materialize root base temporary
        Checker.Corrections.validate project temporary root event (some base)
    | _ => throw <| IO.userError "explicit --fixture-dirs or --correction-event mode is required"
  catch error => throw <| IO.userError s!"check-claim-corrections: {error}"

/-- Run the actual selected transition; fixture callbacks cannot override this production interpreter. -/
def selectorEntry (project : FilePath) (args : List String) : IO Unit := do
  try
    let (root,baseRef) ← match args with
      | [root] => pure (FilePath.mk root,"HEAD^")
      | [root,baseRef] => pure (FilePath.mk root,baseRef)
      | _ => throw <| IO.userError "usage: base-diff-ci ROOT [BASE_REF]"
    select root baseRef fun action => match action with
      | .ordinary root baseRef => baseEntry project [root.toString,baseRef]
      | .correction event root baseRef => baseEntry project ["--correction-event",event,root.toString,baseRef]
  catch error => throw <| IO.userError s!"check-base-diff-ci: {error}"

end Checker.Transition
