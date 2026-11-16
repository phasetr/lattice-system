import Lean

/-! Shared infrastructure operations; no mathematical source declarations. -/
namespace Checker.CheckAll
open Lean

/-- Fail without exposing captured HTTP bodies, headers or secret values. -/
def require (b : Bool) (message : String) : IO Unit := unless b do throw <| IO.userError message
/-- Trim command terminators without interpreting contents. -/
def trim (s : String) : String := s.trimAscii.toString
/-- Preserve NUL-separated Git paths, including rename endpoints as add/delete. -/
def split (s sep : String) : Array String := (s.splitOn sep).toArray
/-- Validate a fixed-width lowercase hexadecimal identifier. -/
def hex (s : String) (n : Nat) : Bool := s.length == n && s.toList.all fun c =>
  c.isDigit || ('a' ≤ c && c ≤ 'f')
/-- Read a required JSON field with a bounded diagnostic. -/
def field (j : Json) (k : String) : IO Json := IO.ofExcept <| j.getObjVal? k
/-- Read a required JSON string. -/
def str (j : Json) (k : String) : IO String := do IO.ofExcept <| (← field j k).getStr?
/-- Read a required JSON natural number. -/
def nat (j : Json) (k : String) : IO Nat := do IO.ofExcept <| (← field j k).getNat?
/-- Read a required JSON array. -/
def arr (j : Json) (k : String) : IO (Array Json) := do IO.ofExcept <| (← field j k).getArr?
/-- Object keys are compared as sets, so extra fields do not pass receipt validation. -/
def keys (j : Json) : Array String := match j with
  | .obj o => o.foldl (fun result k _ => result.push k) #[]
  | _ => #[]
/-- Require precisely the specified object fields. -/
def exactKeys (j : Json) (expected : Array String) : Bool :=
  let actual := keys j
  actual.size == expected.size && expected.all actual.contains
/-- Parse untrusted JSON without echoing its contents on failure. -/
def parse (s : String) : IO Json := match Json.parse s with
  | .ok j => pure j
  | .error _ => throw <| IO.userError "invalid evidence JSON"
/-- Run a thin external operation; sensitive input is supplied through stdin only. -/
def output (root : System.FilePath) (cmd : String) (args : Array String)
    (input : Option String := none) : IO String := do
  let p ← IO.Process.output { cmd, args, cwd := some root } input
  require (p.exitCode == 0) s!"external operation failed: {cmd}"
  pure p.stdout
/-- Read Git data without mutating objects, refs or the working tree. -/
def git (root : System.FilePath) (args : Array String) : IO String := output root "git" args
/-- One external gate with inherited output and a mandatory successful exit. -/
structure Command where
  /-- Existing program. -/
  cmd : String
  /-- Arguments never contain the API credential. -/
  args : Array String := #[]
  deriving Inhabited
/-- The shared sequential interpreter makes every current/selected failure fatal. -/
def execute (perform : Command → IO Unit) (plan : Array Command) : IO Unit :=
  plan.forM perform
/-- Run an ordinary verification command; unlike HTTP, no sensitive input is involved. -/
def runGate (root : System.FilePath) (command : Command)
    (childEnvironment : Array (String × Option String) := #[]) : IO Unit := do
  IO.println s!"check-all: run {command.cmd} {String.intercalate " " command.args.toList}"
  let child ← IO.Process.spawn {
    cmd := command.cmd, args := command.args, cwd := some root,
    stdin := .inherit, stdout := .inherit, stderr := .inherit, env := childEnvironment }
  require ((← child.wait) == 0) s!"verification failed: {command.cmd}"
/-- The pinned toolchain supplies its own compiler; caller PATH substitutions do not choose the native backend. -/
def toolchainRoot (root : System.FilePath) : IO System.FilePath := do
  IO.FS.realPath (trim (← output root "lean" #["--print-prefix"]))

/-- Compare whole canonical path components, never a lexical sibling prefix. -/
def pathWithin (path parent : String) : Bool := path == parent || path.startsWith (parent ++ "/")

end Checker.CheckAll
