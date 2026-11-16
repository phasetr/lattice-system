import Checker.Tests.Publication

/-! The single public generation CLI: native derivation, projection, rendering, writing and comparison. -/
namespace Checker.Publication
open Lean System Checker.CheckAll

/-- Mutually exclusive public modes and an optional explicit dataset root. -/
structure Options where
  mode : String := ""
  root : Option String := none
  help : Bool := false

/-- Parse the existing flag interface without spawning another interpreter. -/
def options : List String → Options → Except String Options
  | [], value => if value.help || !value.mode.isEmpty then .ok value else .error "one publication mode is required"
  | "--help" :: _, value | "-h" :: _, value => .ok {value with help := true}
  | "--root" :: root :: rest, value =>
    if Checker.Text.optionToken root then .error "--root requires ROOT"
    else options rest {value with root := some root}
  | ["--root"], _ => .error "--root requires ROOT"
  | ["--"], value => options [] value
  | argument :: rest, value =>
    let key := (argument.splitOn "=").head!
    let choices := #["--write","--check","--test","--derive-source-items","--root","--help"].filter (·.startsWith key)
    if argument.startsWith "--" && choices.size == 1 && choices[0]! == "--root" then
      if argument.contains '=' then options rest {value with root := some (String.intercalate "=" (argument.splitOn "=").tail!)}
      else match rest with
        | root :: tail =>
          if Checker.Text.optionToken root then .error "--root requires ROOT"
          else options tail {value with root := some root}
        | [] => .error "--root requires ROOT"
    else if argument.startsWith "--" && choices.size == 1 && choices[0]! == "--help" && !argument.contains '=' then
      .ok {value with help := true}
    else
      let candidates := #["--write","--check","--test","--derive-source-items"].filter (·.startsWith argument)
      if argument.startsWith "--" && candidates.size == 1 then
        let mode := candidates[0]!
        if value.mode.isEmpty || value.mode == mode then options rest {value with mode}
        else .error "publication modes are mutually exclusive"
      else .error "unknown publication argument"

/-- Run exactly one native publication operation; derivation is read-only and restricted to owned external fixtures. -/
def execute (project : FilePath) (value : Options) : IO Unit := do
  if value.help then
    IO.println "usage: checker --docs (--write | --check | --test | --derive-source-items) [--root ROOT]"
    return
  if value.mode == "--test" then Checker.Tests.Publication.run; return
  require (value.mode != "--derive-source-items" || value.root.isSome) "--derive-source-items requires explicit --root"
  let project ← IO.FS.realPath project
  let requested := value.root.map (fun path => if path.isEmpty then "." else path)
  let root ← IO.FS.realPath (requested.getD project.toString)
  if value.mode == "--derive-source-items" then
    let some ownerText ← IO.getEnv "LATTICE_TEST_ROOT" | throw <| IO.userError "seed derivation requires LATTICE_TEST_ROOT"
    let owner ← IO.FS.realPath ownerText
    require (owner.toString != "/" && !pathWithin project.toString owner.toString &&
      !pathWithin owner.toString project.toString && root != owner && pathWithin root.toString owner.toString)
      "seed derivation requires an owned repository-external fixture"
    let data ← load root #["claims","pages","sources","tracks"]
    let (items,relations) ← derive (← data.rows "claims") (← data.rows "pages") (← data.rows "sources") (← data.rows "tracks")
    let table := fun (name : String) (rows : Array Row) => do
      let header ← headerFor name
      let cells ← rows.mapM fun row => header.mapM (fun key => field row key)
      return Json.mkObj [("header",toJson header),("rows",toJson cells)]
    IO.println (Json.mkObj [("version",toJson (1 : Nat)),("source_items",← table "source_items" items),
      ("item_claims",← table "item_claims" relations)]).compress
    return
  let outputs ← buildOutputs (← publicCatalog (← load root))
  if value.mode == "--write" then
    writeOutputs root outputs
    IO.println s!"generate-public-docs: wrote {outputs.size} files"
  else
    require (← checkOutputs root outputs) "generated documentation differs"
    IO.println s!"generate-public-docs: ok ({outputs.size} files)"

/-- The library entry preserves failure propagation and the original diagnostic prefix. -/
def entry (project : FilePath) (args : List String) : IO Unit := do
  try
    let value ← IO.ofExcept (options args {})
    execute project value
  catch error => throw <| IO.userError s!"generate-public-docs: {error}"

/-- Public usage failures return 2, content failures 1, and successful operations 0. -/
def cli (project : FilePath) (args : List String) : IO UInt32 := do
  match options args {} with
  | .error message => IO.eprintln s!"generate-public-docs: {message}"; return 2
  | .ok value =>
    if value.mode == "--derive-source-items" && value.root.isNone && !value.help then
      IO.eprintln "generate-public-docs: --derive-source-items requires explicit --root"
      return 2
    try execute project value; return 0
    catch error => IO.eprintln s!"generate-public-docs: {error}"; return 1

end Checker.Publication
