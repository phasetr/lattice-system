import Lean

/-!
Shared current-tree and regression dispatcher. Source mathematics stays in the
registered production modules; this program controls verification and evidence.
-/

open Lean

namespace Checker.CheckAll

/-- Current receipt encoding; older dispatcher receipts are never cache evidence. -/
def version : Nat := 2
/-- The sole regression-suite definition. -/
def suites : Array (String × String) := #[
  ("checkers", "test-checkers.sh"), ("skeleton", "test-skeleton-semantic.sh"),
  ("corrections", "test-claim-corrections-runtime.sh"),
  ("content", "test-content-amendments-runtime.sh"), ("selector", "test-base-diff-ci-runtime.sh")]
/-- Registries whose semantic changes require fresh PR regressions. -/
def semanticTables := #["phase", "source-progress", "bindings", "dependencies", "claim-context",
  "axioms", "claim-axioms", "vocabulary", "claim-vocabulary", "modules", "imports",
  "statement-modules", "statement-imports"]
/-- Known corpus-only tables; unknown paths are never silently light. -/
def corpusTables := #["tracks", "sources", "source-invariants", "pages", "claims", "source-items",
  "item-claims", "slices", "claim-vocabulary-review", "correction-events",
  "claim-normalization-reviews", "claim-corrections", "claim-successors",
  "source-item-additions", "claim-content-amendments"]
/-- Policy documents are projected through the exact predicates their checker reads. -/
def policyPaths := #["README.md", "DESIGN.md", ".github/pull_request_template.md"]
/-- Executable/fixture overrides are forbidden on the production CI route. -/
def overrides := #["CHECK_BASE_DIFF", "CHECK_CORRECTIONS", "GENERATE_PUBLIC_DOCS", "LATTICE_TEST_ROOT",
  "LATTICE_SKELETON_CHECKER_DIR", "LATTICE_SKELETON_ACTUAL_OUT", "PYTHONOPTIMIZE", "PYTHONPATH",
  "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS", "ELAN_TOOLCHAIN", "BASH_ENV", "ENV",
  "GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM", "GIT_CONFIG_PARAMETERS"]
/-- Receipt marker occurs exactly once in a successful producing job. -/
def marker := "rewrite-ci-receipt: "

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
/-- Resolve and validate a required commit. -/
def commit (root : System.FilePath) (ref : String) : IO String := do
  let s := trim (← git root #["rev-parse", "--verify", ref ++ "^{commit}"])
  require (hex s 40) "invalid commit"
  pure s
/-- Read exact commit parent identities. -/
def parents (root : System.FilePath) (ref : String) : IO (Array String) := do
  pure <| (split (trim (← git root #["show", "-s", "--format=%P", ref])) " ").filter (!·.isEmpty)
/-- Read the immutable tree identity. -/
def tree (root : System.FilePath) (ref : String) : IO String := do
  pure <| trim (← git root #["rev-parse", ref ++ "^{tree}"])
/-- Hash canonical Lean JSON using the already-used host SHA256 utility. -/
def digest (root : System.FilePath) (j : Json) : IO String := do
  let result ← output root "shasum" #["-a", "256"] (some j.compress)
  let hash := (split (trim result) " ")[0]!
  require (hex hash 64) "SHA256 operation failed"
  pure hash
/-- Git inventory entry, independent of receipt claims. -/
structure Entry where
  /-- Tracked path. -/
  path : String
  /-- Git mode, preserving type and executable changes. -/
  mode : String
  /-- Git object kind. -/
  kind : String
  /-- Immutable object identity. -/
  oid : String
  deriving Inhabited
/-- Read complete tracked file/type/mode inventory. -/
def entries (root : System.FilePath) (ref : String) : IO (Array Entry) := do
  let raw ← git root #["ls-tree", "-r", "-z", ref]
  let mut result := #[]
  for record in split raw "\u0000" do
    if record.isEmpty then continue
    let pair := split record "\t"
    require (pair.size == 2) "invalid Git tree entry"
    let metadata := split pair[0]! " "
    require (metadata.size == 3) "invalid Git tree metadata"
    result := result.push ⟨pair[1]!, metadata[0]!, metadata[1]!, metadata[2]!⟩
  pure result
/-- Registry/docs/policy projections are distinct from executable bytes. -/
def projected (p : String) : Bool := p.startsWith "registry/" || p.startsWith "docs/" || policyPaths.contains p
/-- Independently compute executable/configuration identity. -/
def engine (root : System.FilePath) (rows : Array Entry) : IO String :=
  digest root <| Json.mkObj <| (rows.filter (!projected ·.path)).toList.map fun e =>
    (e.path, toJson #[e.mode, e.kind, e.oid])
/-- Policy projection binds exactly the current reader's meaningful predicates. -/
def policyProjection (path text : String) : Json := Json.mkObj <|
  [("exact_pr", toJson (decide ((text.splitOn "exact PR").length > 1))),
   ("exact_head", toJson (decide ((text.splitOn "exact head SHA").length > 1)))] ++
  if path == ".github/pull_request_template.md" then
    [("unchecked", toJson (decide ((text.splitOn "- [ ] USER ONLY").length > 1))),
     ("checked", toJson ((decide ((text.splitOn "- [x] USER ONLY").length > 1)) ||
                        (decide ((text.splitOn "- [X] USER ONLY").length > 1))))] else []
/-- Require available immutable historical fixture objects, not a shallow-clone guess. -/
def historical (root : System.FilePath) (ref : String) : IO Json := do
  let events ← git root #["show", ref ++ ":registry/correction-events.tsv"]
  let mut ids := #["c6fb1ec6046626e14dd9a65f396a66386fcb9b7b", "cf4a289e7c766554c8821e167eddac2c3e291c2a"]
  for line in (split events "\n").toList.drop 1 do
    let row := split line "\t"
    if row.size ≥ 4 && !ids.contains row[3]! then ids := ids.push row[3]!
  let mut result := []
  for id in ids do
    let resolved ← commit root id
    let objects := (← entries root resolved).filter (·.path.startsWith "registry/")
    let checked ← output root "git" #["cat-file", "--batch-check"]
      (some (String.join (objects.toList.map (·.oid ++ "\n"))))
    let lines := (split checked "\n").filter (!·.isEmpty)
    require (lines.size == objects.size && lines.all fun s =>
      let fields := split s " "; fields.size == 3 && fields[1]! == "blob") "historical fixture missing"
    result := (id, toJson (← tree root resolved)) :: result
  pure <| Json.mkObj result
/-- Canonical input projections keep corpus bodies out of synthetic fixture signatures. -/
def payloads (root : System.FilePath) (rows : Array Entry)
    (headers registry policy history environment : Json) : IO (Json × String) := do
  let executable ← engine root rows
  let common := Json.mkObj [("engine", toJson executable), ("environment", environment),
    ("paths", Json.mkObj (rows.toList.map fun e => (e.path, toJson #[e.mode, e.kind]))),
    ("headers", headers), ("policy", policy)]
  let synthetic ← digest root common
  let corpus ← digest root <| common.mergeObj <| Json.mkObj [("registry", registry), ("historical", history)]
  pure (Json.mkObj <| suites.toList.map fun (name, _) =>
    (name, toJson (if #["checkers", "corrections", "content"].contains name then corpus else synthetic)), executable)

/-- Compute the two conservative actual-input signatures and independent engine hash. -/
def signatures (root : System.FilePath) (ref : String) (env : Json) : IO (Json × String) := do
  let rows ← entries root ref
  let mut headers := []; let mut registry := []; let mut policy := []
  for e in rows do
    require (e.kind == "blob") "non-blob tracked input"
    if e.path.startsWith "registry/" then
      let text ← git root #["show", ref ++ ":" ++ e.path]
      headers := (e.path, toJson (split text "\n")[0]!) :: headers
      registry := (e.path, toJson e.oid) :: registry
    if policyPaths.contains e.path then
      policy := (e.path, policyProjection e.path (← git root #["show", ref ++ ":" ++ e.path])) :: policy
  payloads root rows (Json.mkObj headers) (Json.mkObj registry) (Json.mkObj policy) (← historical root ref) env
/-- Decide whether an ordinary content change belongs to the narrow light surface. -/
def changeForcesFull (path status oldMode newMode : String) (headerChanged : Bool) : Bool :=
  if status != "M" || oldMode != newMode || !#["100644", "100755"].contains newMode then true
  else if path.startsWith "registry/" && path.endsWith ".tsv" then
    let name := ((path.drop 9).toString.dropEnd 4).toString
    semanticTables.contains name || !corpusTables.contains name || headerChanged
  else !#["README.md", "DESIGN.md"].contains path && !path.startsWith "docs/"
/-- Classify every raw-z endpoint; invalid Git operations fail rather than become an empty diff. -/
def fullRequired (root : System.FilePath) (base head : String) : IO Bool := do
  let raw := split (← git root #["diff", "--raw", "--no-renames", "--no-abbrev", "-z", base, head]) "\u0000"
  let mut full : Bool := raw.size ≤ 1
  for i in [:raw.size / 2] do
    let fields := split raw[i*2]! " "
    require (fields.size == 5) "invalid raw Git difference"
    let path := raw[i*2+1]!
    let mut headerChanged := false
    if fields[4]! == "M" && path.startsWith "registry/" && path.endsWith ".tsv" then
      let a ← git root #["show", base ++ ":" ++ path]
      let b ← git root #["show", head ++ ":" ++ path]
      headerChanged := (split a "\n")[0]! != (split b "\n")[0]!
    full := full || changeForcesFull path fields[4]! (fields[0]!.drop 1).toString fields[1]! headerChanged
  pure full

/-- Require an environment value, without putting secret values in diagnostics. -/
def env (key : String) : IO String := do
  let some value ← IO.getEnv key | throw <| IO.userError s!"missing environment key: {key}"
  require (!value.isEmpty) s!"empty environment key: {key}"
  pure value
/-- Bind runner image and installed tool versions for reuse, not local paths or secrets. -/
def environment (root : System.FilePath) : IO Json := do
  let mut fields := []
  for key in #["RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion"] do
    fields := (key, toJson (← env key)) :: fields
  for (name, command) in #[("lean", "lean"), ("lake", "lake"), ("git", "git"), ("bash", "bash"), ("python", "python3"), ("curl", "curl")] do
    let text ← output root command #["--version"]
    fields := (name, toJson (split text "\n")[0]!) :: fields
  pure <| Json.mkObj fields
/-- A push binds payload before/after to the actual single-parent checkout, never origin/HEAD. -/
def pushBound (head base source : String) (actualParents : Array String) : Bool :=
  source == head && hex base 40 && base != String.ofList (List.replicate 40 '0') && actualParents == #[base]
/-- PR acceptance requires the exact synthetic base/source parents in order. -/
def syntheticBound (head base source : String) (actualParents : Array String) : Bool :=
  head != source && actualParents == #[base, source]
/-- Event-bound checkout identity; a production push never compares against its own trunk ref. -/
def context (root : System.FilePath) : IO Json := do
  require ((trim (← git root #["status", "--porcelain"])).isEmpty) "CI checkout must be clean"
  let event ← env "GITHUB_EVENT_NAME"
  let payload ← parse (← IO.FS.readFile (← env "GITHUB_EVENT_PATH"))
  let head ← commit root "HEAD"
  let (base, source) ← if event == "push" then do
    let base ← str payload "before"; let source ← str payload "after"
    require (pushBound head base source (← parents root head)) "push identity mismatch"
    pure (base, source)
  else if event == "pull_request" then do
    let pr ← field payload "pull_request"
    let baseRecord ← field pr "base"; let sourceRecord ← field pr "head"
    let base ← str baseRecord "sha"; let source ← str sourceRecord "sha"
    require ((← str baseRecord "ref") == "rewrite-main" && syntheticBound head base source (← parents root head)) "PR synthetic checkout mismatch"
    require (trim (← git root #["merge-base", base, source]) == base) "PR base is not up to date"
    pure (base, source)
  else throw <| IO.userError "unsupported CI event"
  let _ ← commit root base
  pure <| Json.mkObj [("event", toJson event), ("head", toJson head),
    ("source_head", toJson source), ("base", toJson base), ("tree", toJson (← tree root head))]
/-- Successful loaded evidence, including the actual executed job identity. -/
structure Loaded where
  /-- Parsed receipt after strict independent checks. -/
  receipt : Json
  /-- Producing run, attempt and job. -/
  origin : Json
/-- Bounded repository-only API access; token is never an argument or log value. -/
structure Evidence where
  /-- Exact repository scope. -/
  repository : String
  /-- Ephemeral token held only in memory/stdin. -/
  token : String
  /-- Monotonic deadline for the entire lookup. -/
  deadline : Nat
  /-- Independently expected executable identity. -/
  executable : String
  /-- Avoid repeating original-producer lookups within one verification. -/
  cache : IO.Ref (Array (Nat × Loaded))
/-- Explicit transport flags ignore user curl configuration and never forward cross-host credentials. -/
def curlArguments (repository suffix : String) (timeout : String := "8") : Array String := #["--disable", "--silent", "--show-error", "--fail", "--location",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "5", "--max-time", timeout,
  "--max-filesize", "8000000", "--config", "-", "https://api.github.com/repos/" ++ repository ++ suffix]
/-- Use curl's protected redirect semantics; never use location-trusted. -/
def http (root : System.FilePath) (e : Evidence) (suffix : String) : IO String := do
  let now ← IO.monoMsNow
  require (now < e.deadline) "evidence lookup budget exhausted"
  require (!(e.token.contains '\n') && !(e.token.contains '\r') &&
    !(e.token.contains '"') && !(e.token.contains '\\')) "invalid token encoding"
  let config := s!"header = \"Authorization: Bearer {e.token}\"\nheader = \"Accept: application/vnd.github+json\"\nheader = \"X-GitHub-Api-Version: 2022-11-28\"\n"
  let remaining := min 8000 (e.deadline - now)
  let fraction := (("00" ++ toString (remaining % 1000)).takeEnd 3).toString
  let timeout := s!"{remaining / 1000}.{fraction}"
  let result ← output root "curl" (curlArguments e.repository suffix timeout)
    (some config)
  require (result.utf8ByteSize ≤ 8000000) "oversized evidence"
  pure result
/-- Fetch only a JSON API response in the fixed repository. -/
def api (root : System.FilePath) (e : Evidence) (suffix : String) : IO Json := do parse (← http root e suffix)
/-- Validate the receipt format before considering any cache result. -/
def validReceipt (j : Json) : IO Unit := do
  require (exactKeys j #["version", "run_id", "run_attempt", "head", "source_head", "base", "tree",
    "event", "engine", "environment", "suites", "current", "transition", "build"]) "receipt fields mismatch"
  require ((← nat j "version") == version) "receipt version mismatch"
  for key in #["head", "source_head", "base", "tree"] do require (hex (← str j key) 40) "invalid receipt commit"
  for key in #["current", "transition", "build"] do require ((← str j key) == "success") "fresh gate not successful"
  let results ← field j "suites"
  require (exactKeys results (suites.map Prod.fst)) "suite set mismatch"
  for (name, _) in suites do
    let result ← field results name
    require (exactKeys result #["input", "result", "origin"] && hex (← str result "input") 64) "invalid suite receipt"
    let state ← str result "result"; let origin ← field result "origin"
    if state == "executed" then require origin.isNull "executed suite has foreign origin"
    else
      require (state == "reused" && exactKeys origin #["run_id", "run_attempt", "job_id"]) "invalid suite origin"
      for key in #["run_id", "run_attempt", "job_id"] do require ((← nat origin key) > 0) "invalid origin identity"
/-- Decode exactly one final versioned marker; duplicate or malformed logs are not evidence. -/
def receiptFromLog (log : String) : IO Json := do
  let hits := (split log "\n").filter fun line => (line.splitOn marker).length > 1
  require (hits.size == 1) "receipt marker missing or ambiguous"
  let pieces := split hits[0]! marker
  require (pieces.size == 2) "ambiguous receipt marker"
  let receipt ← parse pieces[1]!
  validReceipt receipt
  pure receipt
/-- Require a successful producer in the exact repository, workflow and event scope. -/
def validateRun (run : Json) (repository : String) (runId : Nat) : IO Nat := do
  require (runId > 0 && (← nat run "id") == runId && (← str run "status") == "completed" &&
    (← str run "conclusion") == "success" && (← str run "name") == "rewrite-ci" &&
    (← str run "path") == ".github/workflows/rewrite-ci.yml" &&
    (← str (← field run "repository") "full_name") == repository) "untrusted producing run"
  let event ← str run "event"
  require (event == "push" || event == "pull_request") "invalid producing event"
  if event == "push" then require ((← str run "head_branch") == "rewrite-main") "nonproduction push evidence"
  let attempt ← nat run "run_attempt"
  require (attempt > 0) "invalid attempt"
  pure attempt
/-- Require the exact successful job, not a skipped or previous-attempt result. -/
def validateJob (job : Json) (runId attempt : Nat) : IO Nat := do
  require ((← str job "name") == "verify" && (← str job "status") == "completed" &&
    (← str job "conclusion") == "success" && (← nat job "run_id") == runId &&
    (← nat job "run_attempt") == attempt) "unsuccessful verification job"
  let id ← nat job "id"
  require (id > 0) "invalid job identity"
  pure id
/-- Bind decoded receipt data to the successful server-side producer. -/
def validateIdentity (receipt run : Json) (runId attempt : Nat) (executable : String) : IO Unit := do
  require ((← nat receipt "run_id") == runId && (← nat receipt "run_attempt") == attempt &&
    (← str receipt "source_head") == (← str run "head_sha") &&
    (← str receipt "event") == (← str run "event") &&
    (← str receipt "engine") == executable) "receipt identity mismatch"
/-- Check actual parents/tree; a direct PR head is not a synthetic-checkout receipt. -/
def validateCheckout (receipt : Json) (actualParents : Array String) (actualTree : String) : IO Unit := do
  require (actualTree == (← str receipt "tree")) "checkout tree mismatch"
  let base ← str receipt "base"; let source ← str receipt "source_head"; let head ← str receipt "head"
  require (if (← str receipt "event") == "push" then pushBound head base source actualParents
    else syntheticBound head base source actualParents) "producing checkout ancestry mismatch"

/-- Load a single successful actual run/attempt/job and independently verify its executable tree. -/
def load (root : System.FilePath) (e : Evidence) (runId : Nat) : IO Loaded := do
  for (id, value) in ← e.cache.get do if id == runId then return value
  let run ← api root e s!"/actions/runs/{runId}"
  let attempt ← validateRun run e.repository runId
  let jobs ← api root e s!"/actions/runs/{runId}/attempts/{attempt}/jobs?per_page=100"
  let records ← arr jobs "jobs"
  require ((← nat jobs "total_count") == 1 && records.size == 1) "ambiguous verification job"
  let job := records[0]!
  let jobId ← validateJob job runId attempt
  let log ← http root e s!"/actions/jobs/{jobId}/logs"
  let receipt ← receiptFromLog log
  validateIdentity receipt run runId attempt e.executable
  let checkout ← api root e ("/git/commits/" ++ (← str receipt "head"))
  let actualParents ← (← arr checkout "parents").mapM fun parent => str parent "sha"
  validateCheckout receipt actualParents (← str (← field checkout "tree") "sha")
  let remote ← api root e ("/git/trees/" ++ (← str receipt "tree") ++ "?recursive=1")
  require ((← field remote "truncated") == Json.bool false) "truncated executable tree"
  let mut rows := #[]
  for row in ← arr remote "tree" do
    let kind ← str row "type"
    if kind != "tree" then rows := rows.push ⟨← str row "path", ← str row "mode", kind, ← str row "sha"⟩
  require ((← engine root rows) == e.executable) "producer executable bytes mismatch"
  let origin := Json.mkObj [("run_id", toJson runId), ("run_attempt", toJson attempt), ("job_id", toJson jobId)]
  let value := Loaded.mk receipt origin
  e.cache.modify (·.push (runId, value))
  pure value
/-- Bind each API candidate explicitly to the independently identified source head. -/
def candidates (root : System.FilePath) (e : Evidence) (ctx : Json) : IO (Array (Nat × String)) := do
  let event ← str ctx "event"
  let source ← if event == "pull_request" then str ctx "base" else do
    let pulls ← api root e ("/commits/" ++ (← str ctx "head") ++ "/pulls?per_page=10")
    let mut hits := #[]
    for pr in ← IO.ofExcept pulls.getArr? do
      let base ← field pr "base"; let head ← field pr "head"; let repo ← field head "repo"
      if !(← field pr "merged_at").isNull && (← str pr "merge_commit_sha") == (← str ctx "head") &&
        (← str base "ref") == "rewrite-main" && !repo.isNull && (← str repo "full_name") == e.repository then
        hits := hits.push (← str head "sha")
    require (hits.size == 1) "no unique merged PR evidence"
    pure hits[0]!
  require (hex source 40) "invalid candidate source"
  let kind := if event == "pull_request" then "push" else "pull_request"
  let result ← api root e s!"/actions/workflows/rewrite-ci.yml/runs?event={kind}&head_sha={source}&per_page=5"
  let mut found := #[]
  for run in ← arr result "workflow_runs" do
    if (← str run "status") == "completed" && (← str run "conclusion") == "success" then
      found := found.push ((← nat run "id"), source)
  pure <| found.extract 0 5
/-- PR engine changes require execution; an exact newly-tested postmerge tree may reuse. -/
def lookupAllowed (full : Bool) (event : String) : Bool := !full || event == "push"
/-- Every candidate is bound to its independently identified source, environment and checkout role. -/
def candidateBound (receipt ctx : Json) (source : String) (environment : Json) : IO Bool := do
  if (← field receipt "environment") != environment || (← str receipt "source_head") != source then return false
  if (← str ctx "event") == "pull_request" then
    return (← str receipt "head") == (← str ctx "base") && (← str receipt "event") == "push"
  return (← str receipt "event") == "pull_request" && (← str receipt "base") == (← str ctx "base") &&
    (← str receipt "tree") == (← str ctx "tree")
/-- Only an exact directly executed origin is reusable; no recursive receipt chain is accepted. -/
def originalBound (original : Loaded) (expected : Json) (name signature : String) (environment : Json) : IO Bool := do
  if original.origin != expected || (← field original.receipt "environment") != environment then return false
  return (← field (← field original.receipt "suites") name) == Json.mkObj [
    ("input", toJson signature), ("result", toJson "executed"), ("origin", Json.null)]
/-- Explicit full mode never reuses regressions; current mode never claims to have run them. -/
def regressionRequired (mode : String) (accepted : Json) (name : String) : Bool :=
  mode != "--current" && (mode == "--full" || (accepted.getObjValD name).isNull)

/-- Reuse only direct original executed results; malformed or unavailable evidence executes instead. -/
def reuse (root : System.FilePath) (e : Evidence) (ctx sigs environment : Json) : IO Json := do
  let mut accepted := Json.mkObj []
  for (id, source) in ← candidates root e ctx do
    try
      let candidate ← load root e id
      let j := candidate.receipt
      if !(← candidateBound j ctx source environment) then continue
      for (name, _) in suites do
        let result ← field (← field j "suites") name
        let signature ← str sigs name
        if (← str result "input") != signature then continue
        let mut origin := candidate.origin
        if (← str result "result") == "reused" then
          let expected ← field result "origin"
          let original ← load root e (← nat expected "run_id")
          if !(← originalBound original expected name signature environment) then continue
          origin := original.origin
        accepted := accepted.setObjVal! name origin
      if (keys accepted).size == suites.size then break
    catch _ => pure ()
  pure accepted

/-- One external gate with inherited output and a mandatory successful exit. -/
structure Command where
  /-- Existing program. -/
  cmd : String
  /-- Arguments never contain the API credential. -/
  args : Array String := #[]
  deriving Inhabited
/-- The sole current-data gate plan shared by every mode. -/
def currentPlan (root : System.FilePath) (phase : String) (moduleRows : Nat) : Array Command := Id.run do
  let mut plan := #[ ]
  for gate in #["tree", "schema", "sources", "order", "lifecycle", "registry", "census", "source-items", "policy"] do
    plan := plan.push ⟨"scripts/check-" ++ gate ++ ".sh", #[root.toString]⟩
  if phase == "vocabulary" || moduleRows > 1 then plan := plan.push ⟨"scripts/check-vocabulary.sh", #[root.toString]⟩
  plan := plan.push ⟨"scripts/check-skeleton.sh", #[root.toString]⟩
  for mode in #["--test", "--check"] do
    plan := plan.push ⟨"python3", #["scripts/generate-public-docs.py", mode, "--root", root.toString]⟩
  return plan
/-- The shared sequential interpreter makes every current/selected failure fatal. -/
def execute (perform : Command → IO Unit) (plan : Array Command) : IO Unit :=
  plan.forM perform
/-- Run an ordinary verification command; unlike HTTP, no sensitive input is involved. -/
def runGate (root : System.FilePath) (command : Command) : IO Unit := do
  IO.println s!"check-all: run {command.cmd} {String.intercalate " " command.args.toList}"
  let child ← IO.Process.spawn {
    cmd := command.cmd, args := command.args, cwd := some root,
    stdin := .inherit, stdout := .inherit, stderr := .inherit }
  require ((← child.wait) == 0) s!"verification failed: {command.cmd}"
/-- Normalize only Lake's own environment, rejecting arbitrary fixture/executable overrides. -/
def validateOverrides (root : System.FilePath) : IO Unit := do
  let lakeKeys := #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN"]
  for key in overrides do
    if !lakeKeys.contains key then require ((← IO.getEnv key).isNone) s!"CI override forbidden: {key}"
  let declared := trim (← IO.FS.readFile (root / "lean-toolchain"))
  require ((← IO.getEnv "ELAN_TOOLCHAIN") == some declared) "noncanonical declared Elan toolchain"
  for key in #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"] do
    let expected ← IO.Process.output {
      cmd := "lake", args := #["env", "printenv", key], cwd := some root,
      env := lakeKeys.map (fun name => (name, none)) }
    require (expected.exitCode == 0 && (← IO.getEnv key) == some (trim expected.stdout))
      s!"noncanonical Lake environment: {key}"
/-- Parsed public CLI; no generic command or credential-injection option exists. -/
structure Options where
  /-- Current/full/CI/self-test. -/
  mode : String := ""
  /-- Explicit local comparison base. -/
  base : String := "origin/rewrite-main"
/-- Reject ambiguous or unsupported modes rather than silently selecting a partial check. -/
def options : List String → Options → Except String Options
  | [], o => if #["--current", "--full", "--ci", "--self-test"].contains o.mode then .ok o else .error "choose a mode"
  | "--base" :: base :: rest, o => options rest {o with base}
  | mode :: rest, o => if #["--current", "--full", "--ci", "--self-test"].contains mode && o.mode.isEmpty then
      options rest {o with mode} else .error "unknown or repeated mode"
/-- A failed or absent signature/evidence calculation leaves every regression required. -/
structure Selection where
  /-- Suite signatures, or null when inputs could not be established. -/
  sigs : Json := Json.null
  /-- Executable hash only when actually established. -/
  executable : String := ""
  /-- Validated runtime identity, or null. -/
  runtime : Json := Json.null
  /-- Only already-validated direct origins may populate this object. -/
  accepted : Json := Json.mkObj []
/-- The same fallback catches unavailable HTTP, malformed evidence and missing historical input. -/
def orFull (operation : IO Selection) : IO Selection := do
  try operation catch _ =>
    IO.println "check-all: accepted input evidence unavailable; execute required regressions"
    pure {}
/-- Compute CI selection without mutating or reusing partially established state on failure. -/
def calculateSelection (root : System.FilePath) (ctx : Json) (full : Bool) : IO Selection := do
  let runtime ← environment root
  let (sigs, executable) ← signatures root (← str ctx "head") runtime
  let mut accepted := Json.mkObj []
  if lookupAllowed full (← str ctx "event") then
    let repository ← env "GITHUB_REPOSITORY"
    let parts := split repository "/"
    require (parts.size == 2 && parts.all fun s => !s.isEmpty && s.toList.all fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-' || c == '.')) "invalid repository scope"
    let cache ← IO.mkRef #[]
    let e : Evidence := ⟨repository, ← env "GH_TOKEN", (← IO.monoMsNow) + 45000, executable, cache⟩
    accepted ← reuse root e ctx sigs runtime
  pure ⟨sigs, executable, runtime, accepted⟩

/-- Self-test assertion count, including expected rejection cases. -/
def expect (counter : IO.Ref Nat) (b : Bool) (name : String) : IO Unit := do
  require b ("self-test failed: " ++ name)
  counter.modify (·+1)
/-- A negative case passes only when the production validator actually rejects it. -/
def reject (counter : IO.Ref Nat) (action : IO α) (name : String) : IO Unit := do
  let failed ← try let _ ← action; pure false catch _ => pure true
  expect counter failed name
/-- Minimal valid synthetic receipt, independent of the actual mathematical corpus. -/
def fixtureReceipt : Json := Json.mkObj [
  ("version", toJson version), ("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)),
  ("head", toJson (String.ofList (List.replicate 40 'a'))),
  ("source_head", toJson (String.ofList (List.replicate 40 'c'))),
  ("base", toJson (String.ofList (List.replicate 40 'b'))),
  ("tree", toJson (String.ofList (List.replicate 40 'd'))), ("event", toJson "pull_request"),
  ("engine", toJson "engine"), ("environment", Json.mkObj []),
  ("current", toJson "success"), ("transition", toJson "success"), ("build", toJson "success"),
  ("suites", Json.mkObj (suites.toList.map fun (name, _) => (name, Json.mkObj [
    ("input", toJson (String.ofList (List.replicate 64 '1'))), ("result", toJson "executed"), ("origin", Json.null)])))]
/-- Fast negative and positive tests cover dispatch, schema, ancestry, scope and secrecy. -/
def selfTest (root : System.FilePath) : IO Unit := do
  let count ← IO.mkRef 0
  expect count ((Json.mkObj [("z", toJson "last"), ("a", toJson "first")]).compress ==
    (Json.mkObj [("a", toJson "first"), ("z", toJson "last")]).compress) "canonical JSON key order"
  for status in #["A", "D", "T", "R100"] do
    expect count (changeForcesFull "README.md" status "100644" "100644" false) "all raw endpoints"
  for (path, oldMode, newMode, header) in #[
    ("unknown", "100644", "100644", false), ("registry/new.tsv", "100644", "100644", false),
    ("README.md", "100644", "100755", false), ("README.md", "100644", "120000", false),
    ("registry/claims.tsv", "100644", "100644", true),
    ("registry/bindings.tsv", "100644", "100644", false),
    ("Checker/CheckAll.lean", "100644", "100644", false)] do
    expect count (changeForcesFull path "M" oldMode newMode header) "full fallback input"
  expect count (!changeForcesFull "registry/claims.tsv" "M" "100644" "100644" false) "known corpus edit"
  expect count (policyProjection "README.md" "exact PR exact head SHA prose" ==
    policyProjection "README.md" "different prose exact PR exact head SHA") "policy prose projection"
  expect count (policyProjection "README.md" "no gate" != policyProjection "README.md" "exact PR exact head SHA") "policy predicates"
  for (phase, rows, needed) in #[("bootstrap", 1, false), ("vocabulary", 1, true), ("census", 2, true)] do
    expect count ((currentPlan root phase rows).any (·.cmd == "scripts/check-vocabulary.sh") == needed) "semantic current selection"
  for mode in #["--current", "--full", "--ci", "--self-test"] do
    expect count ((options [mode] {}).isOk) "known CLI mode"
  for args in [[], ["--current", "--full"], ["--unknown"], ["--base"]] do
    expect count (!(options args {}).isOk) "invalid CLI rejected"
  validReceipt fixtureReceipt
  expect count true "valid receipt"
  for fieldName in #["version", "head", "source_head", "base", "tree", "current", "transition", "build", "suites"] do
    reject count (validReceipt (fixtureReceipt.setObjVal! fieldName Json.null)) "missing or invalid receipt field"
  reject count (validReceipt (fixtureReceipt.setObjVal! "version" (toJson (1 : Nat)))) "old schema cannot be evidence"
  reject count (validReceipt (fixtureReceipt.setObjVal! "extra" Json.null)) "unknown receipt field"
  let run := Json.mkObj [("id", toJson (7 : Nat)), ("status", toJson "completed"), ("conclusion", toJson "success"),
    ("name", toJson "rewrite-ci"), ("path", toJson ".github/workflows/rewrite-ci.yml"),
    ("repository", Json.mkObj [("full_name", toJson "owner/repo")]), ("event", toJson "pull_request"),
    ("run_attempt", toJson (2 : Nat)), ("head_sha", ← field fixtureReceipt "source_head")]
  let _ ← validateRun run "owner/repo" 7
  for (key, value) in #[("status", "in_progress"), ("conclusion", "cancelled"), ("conclusion", "failure"),
    ("conclusion", "skipped"), ("name", "other"), ("path", "other.yml"), ("event", "workflow_dispatch")] do
    reject count (validateRun (run.setObjVal! key (toJson value)) "owner/repo" 7) "unsuccessful or foreign producer"
  reject count (validateRun run "foreign/repo" 7) "foreign repository"
  let job := Json.mkObj [("id", toJson (11 : Nat)), ("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)),
    ("name", toJson "verify"), ("status", toJson "completed"), ("conclusion", toJson "success")]
  let _ ← validateJob job 7 2
  for result in #["cancelled", "skipped", "failure", "timed_out", "neutral"] do
    reject count (validateJob (job.setObjVal! "conclusion" (toJson result)) 7 2) "job must actually succeed"
  reject count (validateJob job 7 1) "attempt mismatch"
  reject count (validateJob job 8 2) "run mismatch"
  validateIdentity fixtureReceipt run 7 2 "engine"
  for changed in #[fixtureReceipt.setObjVal! "run_id" (toJson (8 : Nat)),
    fixtureReceipt.setObjVal! "source_head" (← field fixtureReceipt "head"),
    fixtureReceipt.setObjVal! "engine" (toJson "foreign")] do
    reject count (validateIdentity changed run 7 2 "engine") "receipt producer binding"
  let base ← str fixtureReceipt "base"; let source ← str fixtureReceipt "source_head"; let actualTree ← str fixtureReceipt "tree"
  validateCheckout fixtureReceipt #[base, source] actualTree
  reject count (validateCheckout fixtureReceipt #[base] actualTree) "wrong synthetic parent"
  reject count (validateCheckout (fixtureReceipt.setObjVal! "head" (toJson source)) #[base, source] actualTree) "direct PR head rejected"
  reject count (validateCheckout fixtureReceipt #[base, source] base) "tree mismatch"
  let plan := currentPlan root "vocabulary" 3 ++
    #[⟨"scripts/check-base-diff-ci.sh", #[root.toString, base]⟩] ++
    suites.map (fun (_, script) => ⟨"scripts/" ++ script, #[root.toString]⟩) ++ #[⟨"lake", #["build"]⟩]
  for target in [:plan.size] do
    let calls ← IO.mkRef 0
    reject count (execute (fun _ => do
      let index ← calls.get; calls.modify (·+1)
      require (index != target) "injected selected failure") plan) "every current/selected failure propagates"
    expect count ((← calls.get) == target + 1) "no commands after failed gate"
  let cache ← IO.mkRef #[]
  let e : Evidence := ⟨"owner/repo", "fixture", 0, "engine", cache⟩
  reject count (http root e "/actions/runs/7") "expired lookup does not contact network"
  reject count (output root "sh" #["-c", "exit 7"]) "external exit is mandatory"
  expect count (pushBound source base source #[base]) "push actual before"
  expect count (!pushBound source source source #[base]) "origin equal HEAD is not push before"
  expect count (!pushBound source (String.ofList (List.replicate 40 '0')) source #[base]) "zero before rejected"
  expect count (!pushBound source base source #[base, source]) "ambiguous push parents rejected"
  let _ ← receiptFromLog ("timestamp " ++ marker ++ fixtureReceipt.compress)
  for text in #["no marker", marker ++ "invalid", marker ++ fixtureReceipt.compress ++ "\n" ++ marker ++ fixtureReceipt.compress] do
    reject count (receiptFromLog text) "missing malformed duplicate marker"
  expect count (!lookupAllowed true "pull_request" && lookupAllowed true "push") "new PR engine full and exact postmerge lookup"
  let ctx := Json.mkObj [("event", toJson "push"), ("base", toJson base), ("tree", toJson actualTree)]
  let envJson ← field fixtureReceipt "environment"
  expect count (← candidateBound fixtureReceipt ctx source envJson) "exact postmerge candidate"
  expect count (!(← candidateBound fixtureReceipt ctx base envJson)) "different source same tree rejected"
  expect count (!(← candidateBound fixtureReceipt (ctx.setObjVal! "base" (toJson source)) source envJson)) "actual before mismatch"
  let origin := Json.mkObj [("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)), ("job_id", toJson (11 : Nat))]
  let original : Loaded := ⟨fixtureReceipt, origin⟩
  let signature := String.ofList (List.replicate 64 '1')
  expect count (← originalBound original origin "skeleton" signature envJson) "direct executed original"
  for key in #["run_attempt", "job_id"] do
    expect count (!(← originalBound original (origin.setObjVal! key (toJson (99 : Nat))) "skeleton" signature envJson)) "original job or attempt mismatch"
  let recursive := fixtureReceipt.setObjVal! "suites" <|
    (fixtureReceipt.getObjValD "suites").setObjVal! "skeleton" <| Json.mkObj [
      ("input", toJson signature), ("result", toJson "reused"), ("origin", origin)]
  expect count (!(← originalBound ⟨recursive, origin⟩ origin "skeleton" signature envJson)) "recursive original rejected"
  expect count (!(← originalBound original origin "skeleton" "other" envJson)) "original input mismatch"
  for label in #["API unavailable", "historical fixture unavailable"] do
    let selected ← orFull (throw <| IO.userError label)
    expect count (suites.all fun (name, _) => regressionRequired "--ci" selected.accepted name) "lookup and history failure require all suites"
  let allAccepted := Json.mkObj (suites.toList.map fun (name, _) => (name, origin))
  expect count (suites.all fun (name, _) => !regressionRequired "--current" allAccepted name) "current coverage stays partial"
  expect count (suites.all fun (name, _) => regressionRequired "--full" allAccepted name) "explicit full cannot reuse"
  let rows : Array Entry := #[⟨"Checker/CheckAll.lean", "100644", "blob", "engine"⟩,
    ⟨".gitignore", "100644", "blob", "ignore"⟩, ⟨"registry/claims.tsv", "100644", "blob", "old"⟩]
  let headers := Json.mkObj [("registry/claims.tsv", toJson "header")]
  let policy := Json.mkObj [("README.md", policyProjection "README.md" "exact PR exact head SHA")]
  let registryA := Json.mkObj [("registry/claims.tsv", toJson "old")]
  let registryB := Json.mkObj [("registry/claims.tsv", toJson "new")]
  let (before, _) ← payloads root rows headers registryA policy (Json.mkObj []) envJson
  let (after, _) ← payloads root rows headers registryB policy (Json.mkObj []) envJson
  for (name, _) in suites do
    expect count ((before.getObjValD name == after.getObjValD name) ==
      (!#["checkers", "corrections", "content"].contains name)) "corpus copy closure and synthetic projection"
  let changedRows := rows.set! 1 ⟨".gitignore", "100644", "blob", "changed"⟩
  let (changed, _) ← payloads root changedRows headers registryA policy (Json.mkObj []) envJson
  expect count (suites.all fun (name, _) => before.getObjValD name != changed.getObjValD name) "gitignore is executable fixture input"
  let changedHeaders := headers.setObjVal! "registry/claims.tsv" (toJson "new header")
  let (changed, _) ← payloads root rows changedHeaders registryA policy (Json.mkObj []) envJson
  expect count (suites.all fun (name, _) => before.getObjValD name != changed.getObjValD name) "registry schema closure"
  let transport := curlArguments "owner/repo" "/actions/jobs/11/logs"
  expect count (transport[0]! == "--disable" && transport.contains "--proto-redir" &&
    !transport.contains "--location-trusted" && !transport.any (fun x => (x.splitOn "Authorization").length > 1)) "curl configuration and credential boundary"
  let badToken : Evidence := ⟨"owner/repo", "invalid\ncredential", (← IO.monoMsNow) + 45000, "engine", cache⟩
  reject count (http root badToken "/actions/runs/7") "credential config injection rejected before HTTP"
  IO.println s!"check-all self-test: {(← count.get)} positive/negative assertions passed"

/-- Execute one mode; CI evidence cannot replace fresh data/transition/build gates. -/
def dispatch (root : System.FilePath) (o : Options) : IO Unit := do
  selfTest root
  if o.mode == "--self-test" then return
  let mut ctx := Json.null
  let mut base := o.base
  let mut selection : Selection := {}
  if o.mode == "--ci" then
    validateOverrides root
    ctx ← context root
    base ← str ctx "base"
    let head ← str ctx "head"
    let full ← fullRequired root base head
    selection ← orFull (calculateSelection root ctx full)
  else base ← commit root base
  let sigs := selection.sigs; let executable := selection.executable
  let runtime := selection.runtime; let accepted := selection.accepted
  let phase := (split (← IO.FS.readFile (root / "registry/phase.tsv")) "\n")[1]!
  let moduleRows := ((split (← IO.FS.readFile (root / "registry/modules.tsv")) "\n").filter (!·.isEmpty)).size
  execute (runGate root) (currentPlan root phase moduleRows)
  runGate root ⟨"scripts/check-base-diff-ci.sh", #[root.toString, base]⟩
  let mut results := Json.mkObj []
  if o.mode != "--current" then
    for (name, script) in suites do
      let origin := accepted.getObjValD name
      if regressionRequired o.mode accepted name then
        runGate root ⟨"scripts/" ++ script, #[root.toString]⟩
      else IO.println s!"check-all: reuse {name} from run {← nat origin "run_id"} job {← nat origin "job_id"}"
      results := results.setObjVal! name <| Json.mkObj [
        ("input", sigs.getObjValD name), ("result", toJson (if origin.isNull then "executed" else "reused")), ("origin", origin)]
  runGate root ⟨"lake", #["build"]⟩
  if o.mode == "--ci" && !sigs.isNull && !runtime.isNull && !executable.isEmpty then
    let receipt := ctx.mergeObj <| Json.mkObj [("version", toJson version),
      ("run_id", toJson ((← env "GITHUB_RUN_ID").toNat!)),
      ("run_attempt", toJson ((← env "GITHUB_RUN_ATTEMPT").toNat!)),
      ("engine", toJson executable), ("environment", runtime), ("suites", results),
      ("current", toJson "success"), ("transition", toJson "success"), ("build", toJson "success")]
    IO.println (marker ++ receipt.compress)
  IO.println (if o.mode == "--current" then
    "check-all: current gates passed; regression acceptance remains required in CI"
    else "check-all: all selected gates passed")

end Checker.CheckAll

/-- Standalone Lean verification entrypoint; any selected failure makes the job fail. -/
def main (args : List String) : IO UInt32 := do
  try
    let o ← IO.ofExcept <| Checker.CheckAll.options args {}
    Checker.CheckAll.dispatch (← IO.currentDir) o
    return 0
  catch error =>
    IO.eprintln s!"check-all: failed: {error}"
    return 1
