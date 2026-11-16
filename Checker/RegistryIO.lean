import Checker.RegistryLayout

/-! Physical registry reads and explicit current, historical and owned-fixture profiles.
The layout module supplies semantic views; this boundary never writes historical input.
-/

namespace Checker.RegistryIO
open Lean System Checker.CheckAll Checker.RegistryLayout

/-- The eight future-stage relations share one typed schema rather than empty production files. -/
def futureNames : Array String := #["slices", "dependencies", "bindings", "claim-context",
  "axioms", "claim-axioms", "statement-modules", "statement-imports"]

/-- Source metadata and phase are read together so neither a mixed layout nor an unknown stage is inferred. -/
def contextNames : Array String := #["sources", "phase", "source-progress", "source-invariants"]

/-- Closed logical table names from the owning caller map to their physical registry paths. -/
def tablePath (name : String) : String := "registry/" ++ name ++ ".tsv"

/-- Read an existing UTF-8 file without changing line endings or substituting invalid characters. -/
def readPhysical (path : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes | throw <| IO.userError "invalid UTF-8 registry input"
  pure text

/-- Keep physical absence separate from a later semantic header-only view. -/
def readFiles (root : FilePath) (names : Array String) (initial : Files := {}) : IO Files :=
  names.foldlM (fun files name => do
    let path := tablePath name
    if files.contains path then return files
    let metadata ← try pure (some (← (root / path).symlinkMetadata))
      catch error => match error with
        | .noFileOrDirectory .. => pure none
        | _ => throw error
    let some metadata := metadata | return files
    require (metadata.type == .file) s!"registry table is not a regular file: {name}"
    pure (files.insert path (← readPhysical (root / path)))) initial

/-- Supply only the context required for the requested semantic tables. -/
def load (root : FilePath) (profile : Profile) (names : Array String) : IO View := do
  let raw ← readFiles root (names ++ contextNames)
  let compact := ((raw[tablePath "sources"]?.getD "").splitOn "\n").headD "" == sourceHeader
  let raw ← if compact then readFiles root futureNames raw else pure raw
  let raw ← if compact && names.contains "source-invariants" then
    readFiles root #["pages", "claims"] raw else pure raw
  normalize raw profile

/-- Ordinary tables retain their original direct read and error boundary. -/
def read (root : FilePath) (name : String) (profile : Profile) : IO String := do
  if name == "sources" || name == "source-items" || name == "source-progress" || name == "source-invariants" || futureNames.contains name then
    let view ← load root profile #[name]
    let some text := view.files[tablePath name]? | throw <| IO.userError s!"missing registry/{name}.tsv"
    pure text
  else readPhysical (root / tablePath name)

/-- Only a separately owned, external regression root can select the legacy fixture profile. -/
def currentProfile (project target : FilePath) : IO Profile := do
  let project ← IO.FS.realPath project
  let target ← IO.FS.realPath target
  if target == project then return .current
  if let some ownerText ← IO.getEnv "LATTICE_TEST_ROOT" then
    let owner ← IO.FS.realPath ownerText
    require (owner.toString != "/" && !pathWithin project.toString owner.toString &&
      !pathWithin owner.toString project.toString && target != owner && pathWithin target.toString owner.toString)
      "legacy registry fixtures require an owned repository-external root"
    return .legacyFixture
  pure .current

end Checker.RegistryIO
