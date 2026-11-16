import Checker.Support

/-! Two-child regression batches with concurrent pipe draining and descriptor-ordered output.
The parent owns plan selection, executable authenticity, source freezing and receipt production.
-/
namespace Checker.RegressionPool
open System Checker.CheckAll

/-- Noninteractive tests never share stdin, and both output streams are captured independently. -/
private def pipeConfig : IO.Process.StdioConfig :=
  {stdin := .null, stdout := .piped, stderr := .piped}

/-- A process owned by exactly one batch worker. -/
private abbrev Child := IO.Process.Child pipeConfig

/-- Preserve already read bytes even when a later read fails. -/
private structure Capture where
  bytes : ByteArray := .empty
  failed : Bool := false

/-- Stop only this worker's process group when a broken reader could otherwise leave a writer blocked. -/
private def stopOwned (child : Child) : IO Unit := do
  try child.kill catch _ => pure ()

/-- Drain one pipe to EOF; on a read error retain its prefix and let the worker reap the terminated child. -/
private partial def drain (child : Child) (handle : IO.FS.Handle) (bytes : ByteArray := .empty) : IO Capture := do
  let chunk ← try pure (some (← handle.read 65536)) catch _ => pure none
  match chunk with
  | none =>
    stopOwned child
    return ⟨bytes,true⟩
  | some chunk =>
    if chunk.isEmpty then return ⟨bytes,false⟩
    drain child handle (bytes ++ chunk)

/-- A wait error is fatal even if terminating and reaping the owned process subsequently succeeds. -/
private def waitOwned (child : Child) : IO (Option UInt32) := do
  try return some (← child.wait)
  catch _ =>
    stopOwned child
    try discard <| child.wait catch _ => pure ()
    return none

/-- The worker returns only after its child and both pipe readers have been joined. -/
private structure Completed where
  status : Option UInt32
  stdout : Capture
  stderr : Capture
  elapsedMs : Nat

/-- A child-spawn exception reaches the task result; every successfully spawned child is explicitly reaped. -/
private def runOne (root exe : FilePath) (name : String) : IO Completed := do
  let started ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := #["--test",name]
    cwd := some root
    stdin := .null
    stdout := .piped
    stderr := .piped
    setsid := true }
  let stdout ← IO.asTask (drain child child.stdout) Task.Priority.dedicated
  let stderr ← IO.asTask (drain child child.stderr) Task.Priority.dedicated
  let status ← waitOwned child
  let out := stdout.get
  let err := stderr.get
  -- The reader itself catches I/O failures; retain unexpected task errors as failed captures too.
  let out := match out with | .ok value => value | .error _ => {failed := true}
  let err := match err with | .ok value => value | .error _ => {failed := true}
  return ⟨status,out,err,(← IO.monoMsNow)-started⟩

/-- Forward a complete stream without decoding, changing bytes, or exposing exception details. -/
private def forward (handle : IO.FS.Stream) (bytes : ByteArray) : IO Bool := do
  try
    handle.write bytes
    handle.flush
    return true
  catch _ => return false

/-- Reproduce stdout then stderr for one descriptor, collecting forwarding errors before rejecting the batch. -/
private def report (failures : Array String) (name : String)
    (result : Except IO.Error Completed) : IO (Array String) := do
  match result with
  | .error _ => return failures.push s!"could not launch regression group: {name}"
  | .ok completed =>
    IO.println s!"check-all timing: regression {name} elapsed_ms={completed.elapsedMs}"
    let out ← forward (← IO.getStdout) completed.stdout.bytes
    let err ← forward (← IO.getStderr) completed.stderr.bytes
    let failures := if completed.status == some 0 then failures else
      failures.push s!"regression group failed: {name}"
    let failures := if completed.stdout.failed || completed.stderr.failed then
      failures.push s!"could not read regression group output: {name}" else failures
    return if out && err then failures else failures.push s!"could not forward regression group output: {name}"

/-- Join all workers before emitting any descriptor's captured streams, including when another spawn failed. -/
private def runBatch (root exe : FilePath) (names : Array String) : IO Unit := do
  let tasks ← names.mapM fun name => IO.asTask (runOne root exe name) Task.Priority.dedicated
  let results ← tasks.mapM fun pending => pure pending.get
  let failures ← (names.zip results).foldlM (fun failures (name,result) => report failures name result) #[]
  require failures.isEmpty (String.intercalate "\n" failures.toList)

/-- Each successful batch advances by two; a failed batch throws before another child is launched. -/
private partial def runFrom (root exe : FilePath) (names : Array String) (offset : Nat) : IO Unit := do
  if offset >= names.size then return
  runBatch root exe (names.extract offset (offset+2))
  runFrom root exe names (offset+2)

/--
Run a registered regression plan in batches of at most two children of the same executable.
The caller supplies its already authenticated canonical executable and validated checkout root,
registered group names, prefetched shared imports, and a frozen source/index/build state.
Each fixed `--test NAME` child owns its own Context, cache and fixture outputs. The pool does not
write shared build state, print command arguments or credentials, or produce reuse receipts.
-/
def runRegressionGroups (root exe : FilePath) (names : Array String) : IO Unit :=
  runFrom root exe names 0

end Checker.RegressionPool
