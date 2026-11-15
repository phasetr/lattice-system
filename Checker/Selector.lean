import Checker.History

/-! Actual event selection depends on Git history, not the registry-validator implementation. -/
namespace Checker.Selector
open Lean System Checker.CheckAll Checker.History

/-- Preserve physical records and only remove the terminal line separator sentinel. -/
def eventLines (text : String) : Array String :=
  if text.isEmpty then #[] else
    let records := split text "\n"
    if text.endsWith "\n" then records.pop else records

/-- Event fields retain the exact one-based TSV coordinates of the production selector. -/
def cell (row : Array String) (position : Nat) : String := row[position-1]?.getD ""

/-- The selector compares only event data records, without normalizing field bytes. -/
def eventRows (text : String) : Array (Array String) :=
  let records := eventLines text
  (records.extract 1 records.size).map (split · "\t")

/-- The actual selector's typed action, injectable only by in-process regression tests. -/
inductive Action where
  | ordinary (root : FilePath) (baseRef : String)
  | correction (event : String) (root : FilePath) (baseRef : String)
  deriving BEq, Repr

/-- Select the event exception from actual Git history, not a caller-supplied mode or shell stub. -/
def select (root : FilePath) (baseRef : String) (perform : Action → IO Unit) : IO Unit := do
  let (root,base) ← actualBase root baseRef
  let path := root / "registry/correction-events.tsv"
  if !(← path.pathExists) then perform (.ordinary root baseRef); return
  let text ← IO.FS.readFile path
  require ((eventLines text)[0]?.getD "" == "event_id\tevent_position\tsource_id\tbase_commit\treview_ref")
    "bad correction-events.tsv header"
  let previous ← if ← hasPath root base "registry/correction-events.tsv" then git root #["show",base ++ ":registry/correction-events.tsv"]
    else pure "event_id\tevent_position\tsource_id\tbase_commit\treview_ref\n"
  let known : Std.HashSet String := (eventRows previous).foldl (fun result row => result.insert (cell row 1)) {}
  let fresh := (eventRows text).filter fun row => !known.contains (cell row 1)
  if fresh.isEmpty then perform (.ordinary root baseRef); return
  require (fresh.size == 1) "multiple new correction events require an explicit CI policy change"
  let event := cell fresh[0]! 1
  require (!event.isEmpty && cell fresh[0]! 4 == base) "new correction event base commit does not match the actual merge base"
  perform (.correction event root baseRef)
  IO.println "check-base-diff-ci: ok"


end Checker.Selector
