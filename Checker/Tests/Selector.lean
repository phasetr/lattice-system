import Checker.Selector
import Checker.Tests.Fixtures

/-! Typed callback regressions over the production event selector's real Git merge-base history. -/
namespace Checker.Tests.Selector
open System Checker.TestSupport Checker.Tests.Fixtures

/-- The exact permanent event header used by the real history selector. -/
def eventHeader : String := "event_id\tevent_position\tsource_id\tbase_commit\treview_ref"

/-- Build the first reviewed event with an explicitly recorded historical base. -/
def firstEvent (base : String) : String :=
  "CORPUS-NORMALIZATION-TASAKI2020-2026\t1\tTASAKI2020\t" ++ base ++ "\tINDEPENDENT-REVIEW"

/-- Stage and commit only the owned fixture event ledger. -/
def commit (ctx : Context) (root : FilePath) (message : String) : IO String := do
  ctx.owned root
  discard <| git root #["add","registry/correction-events.tsv"]
  discard <| git root #["commit","-qm",message]
  pure (← git root #["rev-parse","HEAD"]).trimAscii.toString

/-- Assert one exact typed invocation, including the ordinary/correction arity distinction and immutable arguments. -/
def accepted (ctx : Context) (label : String) (root : FilePath) (base : String)
    (expected : Checker.Selector.Action) : IO Unit := do
  let calls ← IO.mkRef (#[] : Array Checker.Selector.Action)
  expectAction ctx label true (do
    Checker.Selector.select root base fun action => calls.modify (·.push action)
    ensure ((← calls.get) == #[expected]) ("wrong selector mode or arguments: " ++ label)) "" "base-diff-selector"

/-- Require rejection with its exact reached diagnostic before any downstream callback can run. -/
def rejected (ctx : Context) (label : String) (root : FilePath) (base diagnostic : String) : IO Unit := do
  let calls ← IO.mkRef 0
  expectAction ctx label false (Checker.Selector.select root base fun _ => calls.modify (· + 1)) diagnostic "base-diff-selector"
  ensure ((← calls.get) == 0) ("selector invoked a downstream action before rejecting " ++ label)

/-- Run the original six mode-selection cases over actual Git commits and verified merge bases. -/
def run (ctx : Context) : IO Unit := do
  let passed ← ctx.accepted.get
  let failures ← ctx.rejected.get
  let repo := ctx.temporary / "repo"
  newTarget ctx repo
  replace repo "correction-events.tsv" #[eventHeader]
  ctx.owned repo
  discard <| git repo #["init","-q"]
  discard <| git repo #["config","user.name","Runtime Test"]
  discard <| git repo #["config","user.email","runtime@example.invalid"]
  let base ← commit ctx repo "base"
  let first := "CORPUS-NORMALIZATION-TASAKI2020-2026"
  replace repo "correction-events.tsv" #[eventHeader,firstEvent base]
  accepted ctx "new-event-selects-correction" repo base (.correction first repo base)
  let historical ← commit ctx repo "correction"
  accepted ctx "historical-event-uses-normal" repo historical (.ordinary repo historical)
  replace repo "correction-events.tsv" #[eventHeader,firstEvent base,
    "SECOND-CORRECTION\t2\tTASAKI2020\t" ++ historical ++ "\tSECOND-INDEPENDENT-REVIEW"]
  accepted ctx "future-second-event-selects-correction" repo historical (.correction "SECOND-CORRECTION" repo historical)
  discard <| git repo #["reset","-q","--hard",base]
  replace repo "correction-events.tsv" #[eventHeader,firstEvent "0000000000000000000000000000000000000000"]
  rejected ctx "mismatched-base" repo base "does not match the actual merge base"
  replace repo "correction-events.tsv" #[eventHeader,firstEvent base,
    "SECOND-CORRECTION\t2\tTASAKI2020\t" ++ base ++ "\tINDEPENDENT-REVIEW"]
  rejected ctx "multiple-new-events" repo base "multiple new correction events"
  rejected ctx "invalid-base" repo "refs/heads/does-not-exist" "invalid or unfetched base ref"
  ensure ((← ctx.accepted.get) - passed == 3 && (← ctx.rejected.get) - failures == 3)
    "selector matrix differs from six cases (3 positive, 3 negative)"
  IO.println "test-base-diff-ci-runtime: ok (6 cases; 3 positive, 3 negative)"

end Checker.Tests.Selector
