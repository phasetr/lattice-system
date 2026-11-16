import Checker.CheckAll
import Checker.Transition
import Checker.SemanticDriver
import Checker.Regressions

/-! One executable entry for native validators, semantic inspection and verification selection. -/

/-- Dispatch only explicit checker routes; fixture callbacks are never external-command injection. -/
def main (args : List String) : IO UInt32 := do
  try
    let root ← IO.currentDir
    let project := System.FilePath.mk ((← IO.getEnv "LATTICE_CHECK_ALL_PROJECT").getD root.toString)
    match args with
    | "--gate" :: gate :: rest => Checker.CheckAll.dataEntry project gate rest
    | "--docs" :: rest => return ← Checker.Publication.cli project rest
    | "--check" :: route :: rest =>
      match route with
      | "content" => return ← Checker.Content.cli project rest
      | "base-diff" => Checker.Transition.baseEntry project rest
      | "corrections" => Checker.Transition.correctionEntry project rest
      | "base-diff-ci" => Checker.Transition.selectorEntry project rest
      | "vocabulary" => Checker.SemanticDriver.vocabulary project rest
      | "skeleton" => Checker.SemanticDriver.skeleton project rest
      | _ => throw <| IO.userError s!"unknown checker route: {route}"
    | ["--test", name] => Checker.Regressions.run project (← IO.appPath) name
    | _ =>
      let options ← IO.ofExcept <| Checker.CheckAll.options args {}
      Checker.CheckAll.dispatch root options
    return 0
  catch error =>
    IO.eprintln s!"check-all: failed: {error}"
    return 1
