import Lean

/-! Shared process, table and isolation operations for the infrastructure regression suites.
The project supplying checker code and the owned fixture tree are separate identities.
-/

namespace Checker.TestSupport

open Lean System

/-- Exact argument-vector invocation, with an explicit working directory and child-only environment. -/
structure Command where
  cmd : String
  args : Array String := #[]
  cwd : FilePath
  env : Array (String × Option String) := #[]

/-- Regression process results retain both streams and the actual status. -/
abbrev Result := IO.Process.Output

/-- A passed oracle's identity, retained in memory for independent case-roster comparison. -/
structure Observation where
  label : String
  positive : Bool
  route : String
  diagnostic : String
  deriving BEq, Repr

/-- A regression suite's source project, owned temporary root and exact checker executable. -/
structure Context where
  project : FilePath
  temporary : FilePath
  executable : FilePath
  accepted : IO.Ref Nat
  rejected : IO.Ref Nat
  roster : IO.Ref (Array Observation)

/-- Raise an infrastructure error rather than using an optimizable assertion oracle. -/
def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

/-- Compare canonical paths at component boundaries. -/
def within (path parent : FilePath) : Bool :=
  path == parent || path.toString.startsWith (parent.toString ++ "/")

/-- Execute without a shell and retain the exit code and both output streams. -/
def run (command : Command) : IO Result :=
  IO.Process.output { cmd := command.cmd, args := command.args, cwd := some command.cwd, env := command.env }

/-- Require a successful external operation, preserving diagnostics on failure. -/
def checked (command : Command) : IO String := do
  let result ← run command
  ensure (result.exitCode == 0) s!"{command.cmd} exited {result.exitCode}:\n{result.stdout}{result.stderr}"
  pure result.stdout

/-- Write stdin directly to a child pipe, never to argv or a saved temporary credential file. -/
def input (command : Command) (text : String) : IO Result := do
  IO.Process.output { cmd := command.cmd, args := command.args, cwd := some command.cwd, env := command.env } (some text)

/-- Invoke Git against an explicit repository, with no ambient repository selection. -/
def git (root : FilePath) (args : Array String) : IO String :=
  checked ⟨"git", args, root, #[]⟩

/-- Compute the exact Git blob identity of a UTF-8 field without appending a newline. -/
def blob (ctx : Context) (text : String) : IO String := do
  let result ← input ⟨"git", #["hash-object", "--stdin"], ctx.project, #[]⟩ text
  ensure (result.exitCode == 0) s!"hash-object failed: {result.stderr}"
  pure result.stdout.trimAscii.toString

/-- Parse tab-separated fields, retaining trailing empty fields and removing only terminal LF. -/
def rowsOf (text : String) : Array (Array String) :=
  if text.isEmpty then #[] else
  let records := text.splitOn "\n"
  let records := if text.endsWith "\n" then records.dropLast else records
  records.toArray.map fun line => (line.splitOn "\t").toArray

/-- Read a fixture table without stripping carriage returns or Unicode whitespace. -/
def table (root : FilePath) (name : String) : IO (Array (Array String)) :=
  rowsOf <$> IO.FS.readFile (root / "registry" / name)

/-- Write complete TSV rows with the same single-LF record terminator as the original fixtures. -/
def writeTable (root : FilePath) (name : String) (rows : Array (Array String)) : IO Unit := do
  IO.FS.createDirAll (root / "registry")
  IO.FS.writeFile (root / "registry" / name)
    (String.join (rows.toList.map fun row => String.intercalate "\t" row.toList ++ "\n"))

/-- Replace one zero-based fixture column in every matching stable-ID row. -/
def mutate (root : FilePath) (name id : String) (column : Nat) (value : String) : IO Unit := do
  let rows ← table root name
  writeTable root name <| rows.map fun row =>
    if row[0]?.getD "" == id then row.set! column value else row

/-- Append rows to a table without changing its existing bytes. -/
def append (root : FilePath) (name : String) (rows : Array (Array String)) : IO Unit := do
  let path := root / "registry" / name
  let old ← IO.FS.readFile path
  IO.FS.writeFile path <| old ++ String.join
    (rows.toList.map fun row => String.intercalate "\t" row.toList ++ "\n")

/-- Build a child-only fixture environment; production initial overrides remain prohibited. -/
def Context.environment (ctx : Context) : Array (String × Option String) :=
  #[("LATTICE_TEST_ROOT", some ctx.temporary.toString),
    ("LATTICE_CHECK_ALL_PROJECT", some ctx.project.toString)]

/-- Form a typed checker route; no arbitrary fixture executable override is exposed. -/
def Context.command (ctx : Context) (route : String) (args : Array String := #[]) : Command :=
  let environment := if #["vocabulary","skeleton"].contains route && args.contains "--fixture" then
    ctx.environment.push ("LATTICE_SEMANTIC_CACHE",some (ctx.temporary / "semantic-cache").toString)
    else ctx.environment
  ⟨ctx.executable.toString, #["--check", route] ++ args, ctx.project, environment⟩

/-- Invoke one native static gate on a fixture dataset. -/
def Context.gate (ctx : Context) (name : String) (root : FilePath) : Command :=
  ⟨ctx.executable.toString, #["--gate", name, root.toString], ctx.project, ctx.environment⟩

/-- Invoke the existing Python content helper without moving any shell-embedded logic into Python. -/
def Context.content (ctx : Context) (args : Array String) : Command :=
  ⟨"python3", #[ (ctx.project / "scripts/check-content-amendments.py").toString] ++ args,
    ctx.project, ctx.environment⟩

/-- Require the expected status and diagnostic and account for the executed case. -/
def expect (ctx : Context) (label : String) (positive : Bool) (command : Command)
    (diagnostic : String := "") : IO String := do
  let result ← run command
  let output := result.stdout ++ result.stderr
  ensure ((result.exitCode == 0) == positive && (diagnostic.isEmpty ||
      (output.splitOn diagnostic).length > 1))
    s!"unexpected regression result {label} (exit {result.exitCode}):\n{output}"
  if positive then ctx.accepted.modify (· + 1) else ctx.rejected.modify (· + 1)
  let route := if command.cmd == "python3" then
    "content-helper:" ++ command.args[1]?.getD "" else
    command.args[1]?.getD command.cmd
  ctx.roster.modify (·.push ⟨label,positive,route,diagnostic⟩)
  pure output

/-- Exercise an in-process fixture action with the same mandatory, non-optimizable oracle. -/
def expectAction (ctx : Context) (label : String) (positive : Bool) (action : IO Unit)
    (diagnostic : String := "") (route : String := "action") : IO Unit := do
  let result ← try action; pure (none : Option String) catch error => pure (some error.toString)
  ensure (result.isNone == positive && (diagnostic.isEmpty ||
      ((result.getD "").splitOn diagnostic).length > 1))
    s!"unexpected regression action {label}: {result.getD "succeeded"}"
  if positive then ctx.accepted.modify (· + 1) else ctx.rejected.modify (· + 1)
  ctx.roster.modify (·.push ⟨label,positive,route,diagnostic⟩)

/-- Verify that a path belongs to this suite's owned external fixture tree. -/
def Context.owned (ctx : Context) (path : FilePath) : IO Unit := do
  let parent ← IO.FS.realPath ctx.temporary
  let project ← IO.FS.realPath ctx.project
  ensure (!within parent project && !within project parent && parent.toString != "/")
    "fixture temporary root must be external and non-ancestral to the project"
  let resolved ← IO.FS.realPath path
  ensure (within resolved parent && resolved != parent) "fixture path is outside the owned temporary root"

/-- Establish the canonical owning parent before creating a new fixture path. -/
def newTarget (ctx : Context) (target : FilePath) : IO Unit := do
  ensure (!(target.toString.splitOn "/").any (fun part => part == ".." || part == "."))
    "fixture target contains a traversal component"
  let some parent := target.parent | throw <| IO.userError "fixture target has no parent"
  let parent ← IO.FS.realPath parent
  let owner ← IO.FS.realPath ctx.temporary
  ensure (within parent owner) "fixture target parent is outside the owned temporary root"
  let alreadyExists ← try
    discard <| target.symlinkMetadata
    pure true
  catch error => match error with
    | .noFileOrDirectory .. => pure false
    | _ => throw error
  ensure (!alreadyExists) "fixture target already exists, including symbolic links"

/-- Copy an owned fixture without dereferencing its shared dependency symlinks. -/
def copyFixture (ctx : Context) (source target : FilePath) : IO Unit := do
  ctx.owned source
  newTarget ctx target
  discard <| checked ⟨"cp", #["-RP", source.toString, target.toString], ctx.project, #[]⟩

/-- Copy just the registered source project's tracked regular files and symlinks. -/
def copyProject (ctx : Context) (target : FilePath) : IO Unit := do
  newTarget ctx target
  IO.FS.createDirAll target
  let paths ← git ctx.project #["ls-files", "-z"]
  for path in paths.splitOn "\x00" do
    unless path.isEmpty do
      let destination := target / path
      if let some parent := destination.parent then IO.FS.createDirAll parent
      discard <| checked ⟨"cp", #["-P", (ctx.project / path).toString, destination.toString], ctx.project, #[]⟩

/-- Clone history without checkout and materialize exactly the source candidate index, including deletions. -/
def copyCandidate (ctx : Context) (target : FilePath) : IO Unit := do
  newTarget ctx target
  let candidate ← git ctx.project #["ls-files","--stage","-z"]
  ensure ((← git ctx.project #["diff","--name-only","-z"]).isEmpty)
    "candidate fixture requires staged working changes"
  discard <| git ctx.project #["clone","--shared","--no-checkout","-q",ctx.project.toString,target.toString]
  ctx.owned target
  discard <| git target #["read-tree","--empty"]
  for record in candidate.splitOn "\x00" do
    unless record.isEmpty do
      let fields := record.splitOn "\t"
      ensure (fields.length == 2) "invalid candidate index record"
      let metadata := fields[0]!.splitOn " "
      ensure (metadata.length == 3 && metadata[2]! == "0" &&
        #["100644","100755"].contains metadata[0]!) "candidate index needs ordinary stage-zero files"
      let relative := fields[1]!
      ensure (!relative.startsWith "/" && !(relative.splitOn "/").contains "..") "unsafe candidate index path"
      let destination := target / relative
      if let some parent := destination.parent then IO.FS.createDirAll parent
      IO.FS.writeFile destination (← git ctx.project #["cat-file","blob",metadata[1]!])
      let executable := metadata[0]! == "100755"
      IO.setAccessRights destination {
        user := {read := true, write := true, execution := executable}
        group := {read := true, execution := executable}
        other := {read := true, execution := executable} }
      ensure ((← git target #["hash-object",destination.toString]).trimAscii.toString == metadata[1]!)
        "candidate blob changed during materialization"
      discard <| git target #["update-index","--add","--cacheinfo",metadata[0]!,metadata[1]!,relative]
  ensure ((← git ctx.project #["ls-files","--stage","-z"]) == candidate &&
    (← git ctx.project #["diff","--name-only","-z"]).isEmpty) "candidate index changed during fixture construction"

/-- Copy only the corpus, allowing the source project or an owned fixture as its origin. -/
def copyRegistry (ctx : Context) (source target : FilePath) : IO Unit := do
  let source ← IO.FS.realPath source
  if source != ctx.project then ctx.owned source
  newTarget ctx target
  IO.FS.createDirAll target
  discard <| checked ⟨"cp", #["-RP", (source / "registry").toString,
    (target / "registry").toString], ctx.project, #[]⟩

/-- Refresh a synthetic corpus census with exact ordered row-plus-LF hashing. -/
def refresh (ctx : Context) (root : FilePath) : IO Unit := do
  let pages ← table root "pages.tsv"
  let claims ← table root "claims.tsv"
  let mut invariants ← table root "source-invariants.tsv"
  for index in [1:invariants.size] do
    let mut row := invariants[index]!
    let source := row[0]!
    let active := claims.extract 1 claims.size |>.filter fun r =>
      r[1]?.getD "" == source && r[11]?.getD "" == "false"
    let sourcePages := pages.extract 1 pages.size |>.filter fun r => r[1]?.getD "" == source
    row := row.set! 2 (toString active.size)
    row := row.set! 3 (toString (active.filter fun r => r[5]?.getD "" != "out_of_scope").size)
    row := row.set! 4 (toString (active.filter fun r => r[6]?.getD "" == "equation").size)
    row := row.set! 5 (toString (sourcePages.filter fun p =>
      !active.any (fun r => r[3]?.getD "" == p[0]?.getD "")).size)
    let selected := (pages.extract 1 pages.size ++ claims.extract 1 claims.size).filter fun r =>
      r[1]?.getD "" == source
    let text := String.join <| selected.toList.map fun r => String.intercalate "\t" r.toList ++ "\n"
    row := row.set! 6 (← blob ctx text)
    invariants := invariants.set! index row
  writeTable root "source-invariants.tsv" invariants

/-- Find the first unused four-digit fixture identity with an explicit prefix. -/
def unusedId (root : FilePath) (name stem : String) : IO String := do
  let rows ← if ← (root / "registry" / name).pathExists then table root name else pure #[]
  let mut index := 1
  while index < 1000000000 do
    let n := toString index
    let id := stem ++ "-" ++ String.ofList (List.replicate (4 - n.length) '0') ++ n
    if !rows.any (fun r => r[0]?.getD "" == id) then return id
    index := index + 1
  throw <| IO.userError "fixture identifier space exhausted"

/-- Initialize an independently retired external fixture context around a single suite. -/
def withContext (project executable : FilePath) (body : Context → IO α) : IO α :=
  IO.FS.withTempDir fun temporary => do
    let project ← IO.FS.realPath project
    let temporary ← IO.FS.realPath temporary
    ensure (!within temporary project && !within project temporary && temporary.toString != "/")
      "invalid external fixture root"
    body ⟨project, temporary, executable, ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef #[]⟩

end Checker.TestSupport
