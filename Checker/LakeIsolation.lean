import Lake
import Lean.Language.Lean
import Lake.Load.Toml

open Lean Lake System

namespace Checker.LakeIsolation

/-- Report a failed default-target or diagnostic-isolation contract. -/
private def fail (message : String) : IO α :=
  throw <| IO.userError s!"default skeleton isolation: {message}"

/-- Use pinned Lean option normalization, including weak and typed options. -/
private def checkDiagnosticOptions (owner : String) (options : LeanOptions) : IO Unit := do
  -- This is Lean's own CLI/Lake normalization: weak unknown options disappear,
  -- weak known names are unprefixed, and string-valued Booleans are parsed.
  let effective ← Lean.Language.Lean.reparseOptions options.toOptions
  for (name, value) in effective do
    if let .ofBool false := value then
      if name == `warningAsError || name.getRoot == `linter || name.getRoot == `warn then
        fail s!"Lake diagnostic option disables {name} in {owner}"
  unless effective.getBool `warningAsError false do
    fail s!"Lake warningAsError is not enabled in {owner}"

/-- Decode the effective Lake configuration without loading or updating a workspace. -/
def check (root : FilePath) : IO Unit := do
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | fail "Lean installation is unavailable"
  let some lake := lake? | fail "Lake installation is unavailable"
  let .ok lakeEnv ← (Lake.Env.compute lake lean elan?).toBaseIO
    | fail "cannot compute the existing Lake environment"
  let some pkg ← (loadTomlConfig {
      lakeEnv, wsDir := root, relConfigFile := "lakefile.toml" }).toBaseIO
    | fail "invalid Lake TOML configuration"
  unless pkg.defaultTargets == #[`LatticeSystem] do fail "default target must be LatticeSystem"
  checkDiagnosticOptions "package" pkg.leanOptions
  unless pkg.config.moreLeanArgs.isEmpty && pkg.config.weakLeanArgs.isEmpty do
    fail "Lake raw Lean arguments are unsupported in package"
  unless pkg.config.extraDepTargets.isEmpty do fail "package extraDepTargets is unsupported"
  unless pkg.config.dynlibs.isEmpty do fail "package dynlibs is unsupported"
  unless pkg.config.plugins.isEmpty do fail "package plugins is unsupported"
  for configured in pkg.leanLibs do
    checkDiagnosticOptions s!"library {configured.name}" configured.leanOptions
    unless configured.config.moreLeanArgs.isEmpty && configured.config.weakLeanArgs.isEmpty do
      fail s!"Lake raw Lean arguments are unsupported in library {configured.name}"
    unless configured.config.needs.isEmpty && configured.config.extraDepTargets.isEmpty do
      fail s!"library needs/extraDepTargets is unsupported: {configured.name}"
    unless configured.config.dynlibs.isEmpty do
      fail s!"library dynlibs is unsupported: {configured.name}"
    unless configured.config.plugins.isEmpty do
      fail s!"library plugins is unsupported: {configured.name}"
  let some lib := pkg.findLeanLib? `LatticeSystem
    | fail "default target is not a Lean library"
  unless lib.config.defaultFacets == #[LeanLib.leanArtsFacet] do
    fail "default library facets must be leanArts"
  let records ← IO.FS.lines (root / "registry/modules.tsv")
  let mut expected : Array (Name × FilePath) := #[]
  for row in records.drop 1 do
    let fields := row.splitOn "\t" |>.toArray
    unless fields.size == 3 do fail "invalid vocabulary module row"
    expected := expected.push (fields[0]!.toName, root / fields[1]!)
  let mut includesRoot := false
  for mod in (← lib.getModuleArray) do
    let some (_, path) := expected.find? (·.1 == mod.name)
      | fail s!"default library selects a statement or unregistered module: {mod.name}"
    unless (← IO.FS.realPath mod.leanFile) == (← IO.FS.realPath path) do
      fail s!"default module source differs from registry: {mod.name}"
    includesRoot := includesRoot || mod.name == `LatticeSystem
  unless includesRoot do fail "default library omits the canonical production root"
  -- Imports can resolve a different provider from a seed's own library. Check
  -- every registered vocabulary module through Lake's actual package resolver,
  -- including modules that are reached only through the canonical root imports.
  for (name, path) in expected do
    let some provider := pkg.findModule? name
      | fail s!"registered vocabulary module has no Lake provider: {name}"
    unless (← IO.FS.realPath provider.leanFile) == (← IO.FS.realPath path) do
      fail s!"Lake vocabulary provider source differs from registry: {name}"
  -- The nondefault Skeleton target must compile those same registered
  -- statement sources, rather than another provider under the same module name.
  for row in (← IO.FS.lines (root / "registry/statement-modules.tsv")).drop 1 do
    let fields := row.splitOn "\t" |>.toArray
    unless fields.size == 3 do fail "invalid statement module row"
    let name := fields[0]!.toName
    let some provider := pkg.findModule? name
      | fail s!"registered statement module has no Lake provider: {name}"
    unless (← IO.FS.realPath provider.leanFile) == (← IO.FS.realPath (root / fields[1]!)) do
      fail s!"Lake statement provider source differs from registry: {name}"
  IO.println "default skeleton isolation: ok"

end Checker.LakeIsolation
