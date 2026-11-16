import Checker.TestSupport

/-! Shared fixture bytes, history and renderer oracles; suite-specific counted actions stay local. -/
namespace Checker.Tests.FixtureSupport
open System Lean Checker.TestSupport

/-- The stable claim used by the production-derived amendment fixtures. -/
def claim : String := "CL-TASAKI2020-0004"


/-- The permanent content provenance schema. -/
def amendmentHeader : Array String := #["amendment_id", "event_id", "correction_id", "claim_id",
  "old_content_oid", "new_content_oid", "page_source_oid", "review_ref"]

/-- Current fixtures can expose an empty locator ledger without attributing it to an old Git tree. -/
def locationHeader : Array String := #["location_amendment_id", "event_id", "correction_id", "claim_id", "item_id",
  "old_claim_locator", "new_claim_locator", "old_item_locator", "new_item_locator", "review_ref"]


/-- The artifact tables whose empty historical schemas can be adapted. -/
def artifactNames : Array String := #["bindings.tsv", "axioms.tsv", "claim-context.tsv",
  "statement-modules.tsv", "statement-imports.tsv"]


/-- The original six-ledger fixture roster; the new locator ledger has its own focused history tests. -/
def historyTables : Array String := #["correction-events.tsv", "claim-normalization-reviews.tsv",
  "claim-corrections.tsv", "claim-successors.tsv", "source-item-additions.tsv", "claim-content-amendments.tsv"]


/-- Fetch a unique stable-ID fixture record, failing explicitly when it is absent. -/
def record (root : FilePath) (name id : String) : IO (Array String) := do
  let rows ← table root name
  match (rows.extract 1 rows.size).find? (fun r => r[0]?.getD "" == id) with
  | some row => pure row
  | none => throw <| IO.userError s!"missing fixture record {name}:{id}"


/-- Remove matching records while preserving the table header. -/
def remove (root : FilePath) (name id : String) (column : Nat := 0) : IO Unit := do
  let rows ← table root name
  writeTable root name <| rows.extract 0 1 ++
    ((rows.extract 1 rows.size).filter fun r => r[column]?.getD "" != id)


/-- Append a single exact TSV row. -/
def add (root : FilePath) (name : String) (row : Array String) : IO Unit :=
  append root name #[row]


/-- Format a synthetic four-digit order component. -/
def pad (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (4 - s.length) '0') ++ s


/-- Insert rows immediately after a matching row. -/
def insertAfter (rows : Array (Array String)) (predicate : Array String → Bool)
    (extra : Array (Array String)) : Array (Array String) :=
  rows.foldl (fun output row =>
    let output := output.push row
    if predicate row then output ++ extra else output) #[]


/-- Adapt only absent or empty old artifact schemas, preserving current-schema bytes. -/
def adaptEmpty (ctx : Context) (target : FilePath) : IO Unit := do
  ctx.owned target
  for name in artifactNames do
    let expected := (← table ctx.project name)[0]!
    if !(← (target / "registry" / name).pathExists) then
      writeTable target name #[expected]
    else
      let recorded ← table target name
      unless recorded[0]? == some expected do
        ensure (recorded.size == 1) s!"cannot migrate populated historical R4 fixture: {name}"
        writeTable target name #[expected]


/-- Materialize historical registry bytes from the rewrite's own Git graph. -/
def cloneCommit (ctx : Context) (commit : String) (target : FilePath) : IO Unit := do
  IO.FS.createDirAll (target / "registry")
  ctx.owned target
  let paths ← git ctx.project #["ls-tree", "-r", "--name-only", commit, "registry"]
  for path in paths.splitOn "\n" do
    unless path.isEmpty do
      IO.FS.writeFile (target / path) (← git ctx.project #["show", commit ++ ":" ++ path])
  unless ← (target / "registry/claim-content-amendments.tsv").pathExists do
    writeTable target "claim-content-amendments.tsv" #[amendmentHeader]
  unless ← (target / "registry/claim-location-amendments.tsv").pathExists do
    writeTable target "claim-location-amendments.tsv" #[locationHeader]
  adaptEmpty ctx target


/-- Read an explicit JSON property or fail with its field context. -/
def property (value : Json) (key : String) : IO Json :=
  match value.getObjVal? key with
  | .ok result => pure result
  | .error error => throw <| IO.userError error


/-- Read an explicit JSON array. -/
def jsonArray (value : Json) : IO (Array Json) :=
  match value.getArr? with
  | .ok result => pure result
  | .error error => throw <| IO.userError error


/-- Read an explicit JSON string. -/
def jsonString (value : Json) : IO String :=
  match value.getStr? with
  | .ok result => pure result
  | .error error => throw <| IO.userError error


/-- Recursively collect generated UTF-8 output with deterministic path ordering. -/
partial def publicText (root : FilePath) : IO String := do
  let entries := (← root.readDir).qsort (fun a b => a.fileName < b.fileName)
  entries.foldlM (fun text entry => do
    let next ← if ← entry.path.isDir then publicText entry.path else IO.FS.readFile entry.path
    pure (text ++ next)) ""


/-- Run the canonical Lean publication generator. -/
def generate (ctx : Context) (root : FilePath) (mode : String := "--write") : IO Unit := do
  discard <| checked (ctx.docs #[mode,"--root",root.toString])


/-- Parse the actual generated public catalog. -/
def catalog (root : FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile (root / "docs/generated/catalog.json")) with
  | .ok value => pure value
  | .error error => throw <| IO.userError error


/-- Select one public item by its registered stable identity. -/
def catalogItem (value : Json) (id : String) : IO Json := do
  for item in ← jsonArray (← property value "items") do
    if (← jsonString (← property item "item_id")) == id then return item
  throw <| IO.userError s!"missing public item {id}"


/-- Install complete registry bytes in an already owned Git fixture. -/
def installRegistry (ctx : Context) (source target : FilePath) : IO Unit := do
  ctx.owned source
  ctx.owned target
  IO.FS.createDirAll (target / "registry")
  for entry in ← (source / "registry").readDir do
    ensure (!(← entry.path.isDir)) "registry fixture contains an unexpected directory"
    IO.FS.writeBinFile (target / "registry" / entry.fileName) (← IO.FS.readBinFile entry.path)


end Checker.Tests.FixtureSupport
