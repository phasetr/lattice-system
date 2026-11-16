import Checker.Publication
import Checker.Inputs
import Checker.Transition
import Checker.SemanticDriver
import Checker.RegressionPool

/-!
Shared current-tree and regression dispatcher. Source mathematics stays in the
registered production modules; this program controls verification and evidence.
-/

open Lean

namespace Checker.CheckAll

/-- Require an environment value, without putting secret values in diagnostics. -/
def env (key : String) : IO String := do
  let some value ← IO.getEnv key | throw <| IO.userError s!"missing environment key: {key}"
  require (!value.isEmpty) s!"empty environment key: {key}"
  pure value
/-- Hash an existing tool without logging its local installation path. -/
def toolDigest (root path : System.FilePath) : IO String := do
  let result ← output root "shasum" #["-a","256",path.toString]
  let hash := (split (trim result) " ")[0]!
  require (hex hash 64) "compiler identity unavailable"
  pure hash
/-- Record image provenance and bind actual runtime/compiler identities independently of local paths. -/
def environment (root : System.FilePath) : IO Json := do
  let fields ← #["RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion"].foldlM (fun fields key => do
    pure ((key,toJson (← env key)) :: fields)) []
  let fields ← #[("lean", "lean"), ("lake", "lake"), ("git", "git"), ("curl", "curl")].foldlM (fun fields (name,command) => do
    let text ← output root command #["--version"]
    pure ((name,toJson (split text "\n")[0]!) :: fields)) fields
  let libc := (split (← output root "ldd" #["--version"]) "\n")[0]!
  require (!libc.isEmpty) "native runtime ABI identity unavailable"
  let fields := ("libc",toJson libc) :: fields
  let sysroot ← toolchainRoot root
  let nativeVersion ← output root (sysroot / "bin/leanc").toString #["--no-default-config","--version"]
  let fields := ("native_compiler", Json.mkObj [
    ("driver",toJson (← toolDigest root (sysroot / "bin/leanc"))),
    ("backend",toJson (← toolDigest root (sysroot / "bin/clang"))),
    ("version",toJson ((split nativeVersion "\n").extract 0 2)),
    ("driver_path",toJson "bin/leanc"), ("backend_path",toJson "bin/clang")]) :: fields
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
  for key in #["current", "transition"] do require ((← str j key) == "success") "fresh gate not successful"
  let build ← field j "build"
  require (exactKeys build #["result","reason","before","after","origin"]) "invalid build selection"
  let buildResult ← str build "result"
  require (#["executed","not_required"].contains buildResult && !(← str build "reason").isEmpty) "invalid build result"
  for key in #["before","after"] do
    let identity ← str build key
    require (identity.isEmpty || hex identity 64) "invalid mathematical projection"
  if buildResult == "not_required" then
    require (hex (← str build "before") 64 && (← str build "before") == (← str build "after")) "unproved mathematical equality"
    let origin ← field build "origin"
    require (exactKeys origin #["run_id","run_attempt","job_id"]) "missing mathematical baseline acceptance"
    for key in #["run_id","run_attempt","job_id"] do require ((← nat origin key) > 0) "invalid mathematical baseline"
  else require ((← field build "origin").isNull) "executed build has foreign origin"
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
  validateIdentity receipt run runId attempt (← str receipt "engine")
  let checkout ← api root e ("/git/commits/" ++ (← str receipt "head"))
  let actualParents ← (← arr checkout "parents").mapM fun parent => str parent "sha"
  validateCheckout receipt actualParents (← str (← field checkout "tree") "sha")
  let remote ← api root e ("/git/trees/" ++ (← str receipt "tree") ++ "?recursive=1")
  require ((← field remote "truncated") == Json.bool false) "truncated executable tree"
  let rows ← (← arr remote "tree").foldlM (fun rows row => do
    let kind ← str row "type"
    if kind != "tree" then return rows.push ⟨← str row "path", ← str row "mode", kind, ← str row "sha"⟩
    else return rows) #[]
  require ((← engine root rows) == (← str receipt "engine")) "producer executable bytes mismatch"
  let origin := Json.mkObj [("run_id", toJson runId), ("run_attempt", toJson attempt), ("job_id", toJson jobId)]
  let value := Loaded.mk receipt origin
  e.cache.modify (·.push (runId, value))
  pure value
/-- Bind each API candidate explicitly to the independently identified source head. -/
def candidates (root : System.FilePath) (e : Evidence) (ctx : Json) : IO (Array (Nat × String)) := do
  let event ← str ctx "event"
  let source ← if event == "pull_request" then str ctx "base" else do
    let pulls ← api root e ("/commits/" ++ (← str ctx "head") ++ "/pulls?per_page=10")
    let hits ← (← IO.ofExcept pulls.getArr?).foldlM (fun hits pr => do
      let base ← field pr "base"; let head ← field pr "head"; let repo ← field head "repo"
      if !(← field pr "merged_at").isNull && (← str pr "merge_commit_sha") == (← str ctx "head") &&
        (← str base "ref") == "rewrite-main" && !repo.isNull && (← str repo "full_name") == e.repository then
        return hits.push (← str head "sha")
      else return hits) #[]
    require (hits.size == 1) "no unique merged PR evidence"
    pure hits[0]!
  require (hex source 40) "invalid candidate source"
  let kind := if event == "pull_request" then "push" else "pull_request"
  let result ← api root e s!"/actions/workflows/rewrite-ci.yml/runs?event={kind}&head_sha={source}&per_page=5"
  let found ← (← arr result "workflow_runs").foldlM (fun found run => do
    if (← str run "status") == "completed" && (← str run "conclusion") == "success" then
      return found.push ((← nat run "id"), source)
    else return found) #[]
  pure <| found.extract 0 5
/-- Unknown differences require execution; an exact tested postmerge tree may still reuse. -/
def lookupAllowed (full : Bool) (event : String) : Bool := !full || event == "push"
/-- Every candidate is bound to its independently identified source, environment and checkout role. -/
def candidateBound (receipt ctx : Json) (source : String) (environment : Json) : IO Bool := do
  if environmentInputs (← field receipt "environment") != environmentInputs environment ||
    (← str receipt "source_head") != source then return false
  if (← str ctx "event") == "pull_request" then
    return (← str receipt "head") == (← str ctx "base") && (← str receipt "event") == "push"
  return (← str receipt "event") == "pull_request" && (← str receipt "base") == (← str ctx "base") &&
    (← str receipt "tree") == (← str ctx "tree")
/-- Only an exact directly executed origin is reusable; no recursive receipt chain is accepted. -/
def originalBound (original : Loaded) (expected : Json) (name signature : String) (environment : Json) : IO Bool := do
  if original.origin != expected ||
    environmentInputs (← field original.receipt "environment") != environmentInputs environment then return false
  return (← field (← field original.receipt "suites") name) == Json.mkObj [
    ("input", toJson signature), ("result", toJson "executed"), ("origin", Json.null)]
/-- Explicit full mode never reuses regressions; current mode never claims to have run them. -/
def regressionRequired (mode : String) (accepted : Json) (name : String) : Bool :=
  mode != "--current" && (mode == "--full" || (accepted.getObjValD name).isNull)

/-- Retain already validated readers on an exception, while stopping that candidate's remaining effects. -/
def settleCandidate (accepted : Json) : Except Unit Json → Json × Bool
  | .ok updated => (updated,true)
  | .error _ => (accepted,false)

/-- Visit the bounded candidate list, returning accepted origins and stopping once all readers are covered. -/
def reuseCandidates (root : System.FilePath) (e : Evidence) (ctx sigs environment : Json) :
    List (Nat × String) → Json → IO Json
  | [], accepted => pure accepted
  | (id,source) :: rest, accepted => do
    let next ← try
      let candidate ← load root e id
      let j := candidate.receipt
      if !(← candidateBound j ctx source environment) then pure accepted else do
        let (completed,_) ← suites.foldlM (fun (accepted,active) (name,_) => do
          if !active then return (accepted,false)
          try
            let result ← field (← field j "suites") name
            let signature ← str sigs name
            if (← str result "input") != signature then return settleCandidate accepted (.ok accepted)
            let origin ← if (← str result "result") == "reused" then do
              let expected ← field result "origin"
              let original ← load root e (← nat expected "run_id")
              if !(← originalBound original expected name signature environment) then pure none
              else pure (some original.origin)
              else pure (some candidate.origin)
            pure (settleCandidate accepted (.ok (origin.map (accepted.setObjVal! name) |>.getD accepted)))
          catch _ => pure (settleCandidate accepted (.error ()))) (accepted,true)
        pure completed
      catch _ => pure accepted
    if (keys next).size == suites.size then pure next
    else reuseCandidates root e ctx sigs environment rest next

/-- Reuse only direct original executed results; malformed or unavailable evidence executes instead. -/
def reuse (root : System.FilePath) (e : Evidence) (ctx sigs environment : Json) : IO Json := do
  reuseCandidates root e ctx sigs environment (← candidates root e ctx).toList (Json.mkObj [])

/-- Semantic and publication checks are shared by all modes; data gates run natively before this plan. -/
def currentPlan (phase : String) (moduleRows : Nat) : Array String :=
  (if phase == "vocabulary" || moduleRows > 1 then #["vocabulary"] else #[]) ++
    #["skeleton","generator-test","generator-check","transition"]

/-- Interpret one explicit current action, without a shell wrapper or arbitrary command route. -/
def currentAction (root : System.FilePath) (base action : String) : IO Unit := do
  match action with
  | "vocabulary" => Checker.SemanticDriver.vocabulary root []
  | "skeleton" => Checker.SemanticDriver.skeleton root []
  | "generator-test" => Checker.Publication.entry root ["--test","--root",root.toString]
  | "generator-check" => Checker.Publication.entry root ["--check","--root",root.toString]
  | "transition" => Checker.Transition.selectorEntry root [root.toString,base]
  | _ => throw <| IO.userError "unknown current action"

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
  /-- Mathematical build depends on its own actual input projection, not the regression engine. -/
  build : BuildSelection := {}
  /-- Direct successful exact-base verification used only to justify unchanged mathematical inputs. -/
  buildOrigin : Json := Json.null
  /-- Why unsuccessful evidence cannot waive a required regression. -/
  reason : String := "no accepted matching input evidence"
/-- The same fallback catches unavailable HTTP, malformed evidence and missing historical input. -/
def orFull (operation : IO Selection) : IO Selection := do
  try operation catch _ =>
    IO.println "check-all: accepted input evidence unavailable; execute required regressions"
    pure {}
/-- A skipped unchanged mathematical build requires a directly successful exact production base. -/
def acceptedBase (root : System.FilePath) (e : Evidence) (base : String) : IO Json := do
  let result ← api root e s!"/actions/workflows/rewrite-ci.yml/runs?event=push&head_sha={base}&per_page=5"
  for run in ← arr result "workflow_runs" do
    try
      let id ← nat run "id"
      let attempt ← validateRun run e.repository id
      require ((← str run "event") == "push" && (← str run "head_sha") == base) "unaccepted mathematical base"
      let jobs ← api root e s!"/actions/runs/{id}/attempts/{attempt}/jobs?per_page=100"
      let records ← arr jobs "jobs"
      require ((← nat jobs "total_count") == 1 && records.size == 1) "ambiguous baseline verification"
      let job ← validateJob records[0]! id attempt
      return Json.mkObj [("run_id",toJson id),("run_attempt",toJson attempt),("job_id",toJson job)]
    catch _ => pure ()
  throw <| IO.userError "no successful exact-base verification"

/-- Compute per-reader acceptance and mathematical build selection as distinct decisions. -/
def calculateSelection (root : System.FilePath) (ctx : Json) (full : Bool) : IO Selection := do
  let repository ← env "GITHUB_REPOSITORY"
  let parts := split repository "/"
  require (parts.size == 2 && parts.all fun value => !value.isEmpty && value.toList.all fun c =>
    c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-' || c == '.')) "invalid repository scope"
  let cache ← IO.mkRef #[]
  let evidence : Evidence := ⟨repository,← env "GH_TOKEN",(← IO.monoMsNow)+45000,"",cache⟩
  let build ← selectBuild root (← str ctx "base") (← str ctx "head")
  let (build,buildOrigin) ← if build.required then pure (build,Json.null) else do
    try pure (build,← acceptedBase root evidence (← str ctx "base"))
    catch _ => pure ({build with required := true, reason := "exact mathematical baseline acceptance unavailable"},Json.null)
  let regressions ← orFull do
    let runtime ← environment root
    let (sigs,executable) ← signatures root (← str ctx "head") runtime
    let accepted ← if lookupAllowed full (← str ctx "event") then do
      try reuse root evidence ctx sigs runtime catch _ => pure (Json.mkObj [])
      else pure (Json.mkObj [])
    return {sigs,executable,runtime,accepted}
  return {regressions with build,buildOrigin,reason := if full then "unknown/destructive input difference" else "actual reader input changed or accepted evidence absent"}

/-- Accept only ordinary Lean module names when forming argv for the existing cache tool. -/
def cacheModule (name : String) : Bool :=
  (name == "Mathlib" || name.startsWith "Mathlib.") && (name.splitOn ".").all fun part =>
    !part.isEmpty && (part.toList.head! == '_' || part.toList.head!.isAlpha) &&
      part.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))

/-- Cache only current semantic imports and the selected groups' explicit external fixture roots. -/
def importRoots (current : Registry.Data) (selected : Array String) : Option (Array String) := do
  let roots ← ((current.table "imports").rows ++ (current.table "statement-imports").rows).foldlM (fun roots row => do
    let imported := Registry.col row 3
    if imported == "Mathlib" || imported.startsWith "Mathlib." then
      if !cacheModule imported then none else some (roots.push imported)
    else some roots) #[]
  let roots ← selected.foldlM (fun roots name => do
    let group ← Checker.Regressions.groups.find? (·.name == name)
    group.mathlibImports.foldlM (fun roots imported =>
      if cacheModule imported then some (roots.push imported) else none) roots) roots
  return distinctPaths roots

/-- Import artifacts are necessary semantic preparation, distinct from the mathematical default build. -/
def prepareImports (root : System.FilePath) (current : Registry.Data) (selected : Array String) : IO Unit := do
  let roots := importRoots current selected
  if roots == some #[] then
    IO.println "check-all: import cache not_required (no Mathlib semantic inputs)"
    return
  let arguments := #["exe","cache","get"] ++ roots.getD #[]
  IO.println (if roots.isSome then "check-all: prepare declared semantic imports and selected fixture imports"
    else "check-all: prepare full declared Mathlib cache (unknown import inputs)")
  let setting ← IO.getEnv "MATHLIB_CACHE_GET_URL"
  let value := match setting with
    | none => some "https://cache.mathlib.org/mathlib4"
    | some "" => none
    | some value => some value
  runGate root ⟨"lake",arguments⟩ #[("MATHLIB_CACHE_GET_URL",value)]

/-- Self-test assertion count, including expected rejection cases. -/
def expect (counter : IO.Ref Nat) (b : Bool) (name : String) : IO Unit := do
  require b ("self-test failed: " ++ name)
  counter.modify (·+1)
/-- A negative case passes only when the production validator actually rejects it. -/
def reject (counter : IO.Ref Nat) (action : IO α) (name : String) : IO Unit := do
  let failed ← try let _ ← action; pure false catch _ => pure true
  expect counter failed name
/-- A regression rejection must reach its original field-specific diagnostic. -/
def rejectMessage (counter : IO.Ref Nat) (action : IO α) (needle : String) : IO Unit := do
  let actual ← try let _ ← action; pure "" catch error => pure s!"{error}"
  expect counter ((actual.splitOn needle).length > 1) ("missing diagnostic: " ++ needle)
/-- Valid metadata isolates type and value diagnostics without relying on unrelated rejection. -/
def selfTestDiagnostics (root : System.FilePath) (counter : IO.Ref Nat) : IO Unit := do
  let id := String.ofList (List.replicate 40 'a')
  let header := fun table => ((Registry.headers.find? (·.1 == table)).map (·.2)).get!
  let table := fun name (rows : Array (Array String)) => Registry.tableFromText <|
    header name ++ "\n" ++ String.join (rows.toList.map (fun row => String.intercalate "\t" row.toList ++ "\n"))
  let claim := #["CL-FIX-0001","FIX","000001.0001","PG-FIX-0001","setup","definition","definition","Fixture setup.",id,"NONE","NONE","false","NONE","NONE","NONE"]
  let binding := #["CL-FIX-0001","LatticeSystem.Claims.Front.Setup","NONE","LatticeSystem.Claims.Front","definition","definition_value",id,id,"definitional","NONE","NONE","NONE","NONE","NONE","review"]
  let bindingData := fun row => Registry.Data.mk root #[
    ("claims",table "claims" #[claim]),
    ("statement-modules",table "statement-modules" #[#["LatticeSystem.Claims.Front","LatticeSystem/Claims/Front.lean","leaf"]]),
    ("bindings",table "bindings" #[row])]
  Registry.bindings (bindingData binding)
  expect counter true "valid isolated binding metadata"
  rejectMessage counter (Registry.bindings (bindingData (binding.set! 6 "ANY"))) "bad statement type OID"
  rejectMessage counter (Registry.bindings (bindingData (binding.set! 7 "ANY"))) "bad statement value OID"
  let vocabulary := #["VO-LS-9001","LatticeSystem.Fixture","LatticeSystem.Vocabulary.Fixture","definition","primary","NONE",id,id,"linear_algebra","none"]
  let vocabularyData := fun row => Registry.Data.mk root #[
    ("modules",table "modules" #[#["LatticeSystem.Vocabulary.Fixture","LatticeSystem/Vocabulary/Fixture.lean","leaf"]]),
    ("vocabulary",table "vocabulary" #[row])]
  Registry.vocabulary (vocabularyData vocabulary)
  expect counter true "valid isolated vocabulary metadata"
  rejectMessage counter (Registry.vocabulary (vocabularyData (vocabulary.set! 6 "ANY"))) "bad vocabulary type OID"
  rejectMessage counter (Registry.vocabulary (vocabularyData (vocabulary.set! 7 "ANY"))) "bad vocabulary declaration OID"
/-- Minimal valid synthetic receipt, independent of the actual mathematical corpus. -/
def fixtureReceipt : Json := Json.mkObj [
  ("version", toJson version), ("run_id", toJson (7 : Nat)), ("run_attempt", toJson (2 : Nat)),
  ("head", toJson (String.ofList (List.replicate 40 'a'))),
  ("source_head", toJson (String.ofList (List.replicate 40 'c'))),
  ("base", toJson (String.ofList (List.replicate 40 'b'))),
  ("tree", toJson (String.ofList (List.replicate 40 'd'))), ("event", toJson "pull_request"),
  ("engine", toJson "engine"), ("environment", Json.mkObj []),
  ("current", toJson "success"), ("transition", toJson "success"), ("build", Json.mkObj [("result",toJson "executed"),("reason",toJson "fixture"),("before",toJson ""),("after",toJson ""),("origin",Json.null)]),
  ("suites", Json.mkObj (suites.toList.map fun (name, _) => (name, Json.mkObj [
    ("input", toJson (String.ofList (List.replicate 64 '1'))), ("result", toJson "executed"), ("origin", Json.null)])))]
/-- Native data/tree boundaries exercise production helpers independently of full runtime fixtures. -/
def selfTestData (root : System.FilePath) (count : IO.Ref Nat) : IO Unit := do
  for target in [:dataGates.size] do
    let visited ← IO.mkRef (#[] : Array String)
    reject count (executeData fun gate => do
      visited.modify (·.push gate)
      if gate == dataGates[target]! then throw <| IO.userError "injected data gate failure") "native data failure is fatal"
    expect count ((← visited.get).size == target + 1) "no native gate executes after failure"
  let absent : Registry.Data := ⟨root,#[]⟩
  reject count (Registry.order absent) "missing order tables do not pass vacuously"
  reject count (Registry.items absent) "missing item tables do not pass vacuously"
  reject count (Registry.lifecycle absent) "missing lifecycle tables do not pass vacuously"
  let phaseData : Registry.Data := ⟨root,#[ ("phase",Registry.tableFromText "phase\nvocabulary\textra\n") ]⟩
  expect count (Registry.phase phaseData == "vocabulary\textra") "phase reader preserves its entire record"
  reject count (Registry.phaseRead ⟨root,#[ ("phase",Registry.tableFromText "phase\nvocabulary") ]⟩) "unterminated second phase record rejected"
  reject count (dataEntry root "tree" ["--fixture"]) "tree fixture argument is explicit"
  reject count (dataEntry root "census" ["--fixture"]) "census fixture argument is explicit"
  let parsed := Registry.tableFromText "a\tb\nvalue\t\n"
  expect count (parsed.rows == #[#["value",""]]) "TSV trailing empty fields preserved"
  expect count ((Registry.tableFromText "a\nb").rows == #[#["b"]]) "unterminated final data row retained"
  expect count (!(Registry.tableFromText "a").headerEnded) "header LF remains required"
  for value in #["\r","x\u007f"," x","x "," x","x "] do
    expect count (!Registry.validField value) "C0 DEL and original edge whitespace rejected"
  for value in #["x y","\u0085x"," x"] do
    expect count (Registry.validField value) "C locale validation does not broaden to Unicode controls"
  expect count (Registry.slugify "A İ B" == "a-b") "ASCII-only source-item slug"
  expect count (Registry.digits "001" && !Registry.digits "001" true) "count and positive-position grammars differ"
  expect count (Registry.orderKey "000001.0001.0001.0001" &&
    !Registry.claimOrder "000001.0001.0001.0001") "order and registry-claim segment grammars differ"
  expect count (Registry.identifier "a'_1" && !Registry.identifier "1a" && !Registry.identifier "é") "ASCII Lean name grammar"
  let id := String.ofList (List.replicate 40 'a')
  let _ ← treeIndex ("100644 " ++ id ++ " 0\tREADME.md\u0000")
  expect count true "live index stage zero accepted"
  for record in #["120000 " ++ id ++ " 0\tREADME.md\u0000", "100644 " ++ id ++ " 2\tREADME.md\u0000", "100644 bad 0\tREADME.md\u0000"] do
    reject count (treeIndex record) "symlink unresolved index or malformed object rejected"
  let _ ← validateTreePaths #["LatticeSystem.lean"] #[] true
  expect count true "header-only bootstrap permits unregistered production root"
  reject count (validateTreePaths #["LatticeSystem.lean"] #["LatticeSystem.lean","LatticeSystem/Missing.lean"] true) "registered missing production module rejected"
  reject count (validateTreePaths #["LatticeSystem/Unknown.lean"] #[] true) "unregistered tracked production module rejected"
  for path in #["scripts/unknown","unexpected.txt","fixtures/x","tex/guide.tex"] do
    reject count (validateTreePaths #[path] #[] true) "closed tree rejects removed or unknown paths"
  validateTreeFixture "/project" "/test/fixture" "/test"
  expect count true "external fixture containment accepted"
  for (target,testRoot) in #[("/project","/project"),("/test/a","/"),("/project/tests/a","/project/tests"),("/outside/a","/test")] do
    reject count (validateTreeFixture "/project" target testRoot) "fixture source root ancestor and escape rejected"
  let reference := Registry.tableFromText <|
    "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes\nTASAKI2020\tref\t.v1\t" ++ id ++ "\t" ++ id ++ "\tpending\tnote\n"
  reject count (Registry.reference ⟨root,#[ ("reference",reference),("phase",Registry.tableFromText "phase\nbootstrap\n") ]⟩)
    "legacy edition starts with ASCII alphanumeric"
  let contexts := Registry.tableFromText "claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref\nCL-FIX-0002\t1\tCL-FIX-0001\tterm_reference\tinherited\treview\n"
  let claimHeader := ((Registry.headers.find? (·.1 == "claims")).map (·.2)).get!
  let claimRows := Registry.tableFromText (claimHeader ++ "\n" ++
    "CL-FIX-0001\tFIX\t000001.0001\tPG-FIX-0001\tsetup\tdefinition\tdefinition\tFixture setup.\t" ++ id ++ "\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n" ++
    "CL-FIX-0002\tFIX\t000001.0002\tPG-FIX-0001\towner\tassertion\ttheorem\tFixture assertion.\t" ++ id ++ "\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE\n")
  let contextData : Registry.Data := ⟨root,#[ ("claims",claimRows),("claim-context",contexts) ]⟩
  reject count (Registry.bindings contextData) "inherited context still requires item registry"
  let withItems := contextData.tables.push ("item-claims",Registry.tableFromText "item_id\tposition\tclaim_id\n")
  Registry.bindings {contextData with tables := withItems}
  expect count true "inherited context with an existing item registry otherwise passes"

/-- Counterfactual Git trees and working bytes exercise the actual mathematical projection without building mathematics. -/
def selfTestInputs (_root : System.FilePath) (count : IO.Ref Nat) : IO Unit := do
  let lake := "name = \"Fixture\"\ndefaultTargets = [\"LatticeSystem\"]\n[[lean_lib]]\nname = \"LatticeSystem\"\n"
  expect count ((← mathematicalLake lake) == lake) "mathematical Lake prefix remains exact"
  expect count ((← mathematicalLake (lake ++ checkerLakeSuffix)) == lake) "known checker targets are outside mathematical build"
  reject count (mathematicalLake (lake ++ checkerLakeSuffix ++ "# unknown\n")) "unknown Lake suffix cannot prove equality"
  reject count (mathematicalLake (lake ++ checkerLakeSuffix ++ checkerLakeSuffix)) "ambiguous Lake suffix cannot prove equality"
  IO.FS.withTempDir fun temporary => do
    let target := temporary / "mathematical-inputs"
    IO.FS.createDirAll (target / "registry")
    IO.FS.createDirAll (target / "LatticeSystem")
    IO.FS.createDirAll (target / "Checker")
    let initial : Array (String × String) := #[
      ("lakefile.toml",lake),("lean-toolchain","pinned\n"),("lake-manifest.json","{}\n"),
      ("LatticeSystem.lean","/-! Projection fixture. -/\n"),("LatticeSystem/A.lean","/-! Projection leaf. -/\n"),
      ("registry/modules.tsv","module\tsource_path\trole\n"),
      ("registry/imports.tsv","module\tposition\timported_module\tis_exported\tis_meta\timport_all\n"),
      ("README.md","original\n"),("Checker/Fixture.lean","/-! Infrastructure fixture. -/\n")]
    for (path,text) in initial do IO.FS.writeFile (target / path) text
    discard <| git target #["init","--quiet"]
    discard <| git target (#["add","--"] ++ initial.map Prod.fst)
    discard <| git target #["-c","user.name=Fixture","-c","user.email=fixture@example.invalid","commit","--quiet","-m","fixture"]
    let base ← commit target "HEAD"
    expect count (!(← selectLocalBuild target base base).required) "identical working mathematical inputs need no build"
    IO.FS.writeFile (target / "README.md") "changed documentation\n"
    IO.FS.writeFile (target / "Checker/Fixture.lean") "/-! Changed infrastructure. -/\n"
    expect count (!(← selectLocalBuild target base base).required) "dirty documentation and checker do not require math build"
    IO.FS.writeFile (target / "lakefile.toml") (lake ++ checkerLakeSuffix)
    expect count (!(← selectLocalBuild target base base).required) "own checker target addition does not require math build"
    for path in #["LatticeSystem.lean","LatticeSystem/A.lean","lean-toolchain","registry/modules.tsv","registry/imports.tsv"] do
      let before ← IO.FS.readFile (target / path)
      IO.FS.writeFile (target / path) (before ++ "changed\n")
      expect count (← (·.required) <$> selectLocalBuild target base base) "dirty mathematical reader forces build"
      IO.FS.writeFile (target / path) before
    IO.FS.writeFile (target / "lakefile.toml") (lake ++ "leanOptions = {}\n")
    expect count (← (·.required) <$> selectLocalBuild target base base) "dirty mathematical configuration forces build"
    IO.FS.writeFile (target / "lakefile.toml") (lake ++ checkerLakeSuffix)
    IO.FS.writeFile (target / "lakefile.lean") "unknown\n"
    expect count (← (·.required) <$> selectLocalBuild target base base) "untracked effective configuration forces build"
    IO.FS.removeFile (target / "lakefile.lean")
    IO.FS.writeFile (target / "LatticeSystem/New.lean") "/-! New mathematical source. -/\n"
    expect count (← (·.required) <$> selectLocalBuild target base base) "untracked mathematical source forces build"
    IO.FS.removeFile (target / "LatticeSystem/New.lean")
    discard <| output target "chmod" #["+x","LatticeSystem/A.lean"]
    expect count (← (·.required) <$> selectLocalBuild target base base) "working mathematical mode change forces build"
    discard <| output target "chmod" #["-x","LatticeSystem/A.lean"]
    discard <| git target #["add","--","README.md","Checker/Fixture.lean","lakefile.toml"]
    discard <| git target #["-c","user.name=Fixture","-c","user.email=fixture@example.invalid","commit","--quiet","-m","tooling"]
    let tooling ← commit target "HEAD"
    expect count (!(← selectBuild target base tooling).required) "committed checker tooling leaves math projection identical"
    discard <| git target #["mv","LatticeSystem/A.lean","LatticeSystem/B.lean"]
    discard <| git target #["-c","user.name=Fixture","-c","user.email=fixture@example.invalid","commit","--quiet","-m","rename"]
    expect count (← (·.required) <$> selectBuild target tooling (← commit target "HEAD")) "same-blob mathematical rename changes build inputs"
  let imports : Registry.Data := ⟨_root,#[
    ("imports",Registry.tableFromText "module\tposition\timported_module\tis_exported\tis_meta\timport_all\nFixture\t1\tMathlib.Init\ttrue\tfalse\tfalse\n"),
    ("statement-imports",Registry.tableFromText "module\tposition\timported_module\tis_exported\tis_meta\timport_all\n") ]⟩
  expect count (importRoots imports #[] == some #["Mathlib.Init"]) "current semantic imports prepare exact roots"
  expect count (importRoots imports #["skeleton-pure"] == some #["Mathlib.Init","Mathlib.LinearAlgebra.Matrix.Defs"]) "selected pure fixtures retain notation imports"
  expect count (importRoots imports #["vocabulary-semantic"] == some #["Mathlib.Data.Nat.Basic","Mathlib.Init"]) "selected vocabulary negative retains its real external import"
  expect count (importRoots ⟨_root,#[]⟩ #[] == some #[]) "known empty import roots skip cache preparation"
  expect count (importRoots imports #["unknown"] == none) "unknown fixture reader requests full cache"
  expect count (!cacheModule "Mathlib.Foo;bad" && !cacheModule "Mathlib..Foo" && cacheModule "Mathlib.Data.Nat.Basic") "cache module arguments are names rather than shell syntax"
  let identity := String.ofList (List.replicate 64 '1')
  let build := Json.mkObj [("result",toJson "not_required"),("reason",toJson "mathematical inputs unchanged"),
    ("before",toJson identity),("after",toJson identity),("origin",Json.mkObj [
      ("run_id",toJson (7 : Nat)),("run_attempt",toJson (2 : Nat)),("job_id",toJson (11 : Nat))])]
  validReceipt (fixtureReceipt.setObjVal! "build" build)
  expect count true "not-required build is typed separately from executed build"
  reject count (validReceipt (fixtureReceipt.setObjVal! "build" (build.setObjVal! "after" (toJson (String.ofList (List.replicate 64 '2')))))) "unequal projection cannot skip build"
  reject count (validReceipt (fixtureReceipt.setObjVal! "build" (build.setObjVal! "origin" Json.null))) "missing baseline acceptance cannot skip build"
  reject count (validReceipt (fixtureReceipt.setObjVal! "build" (build.setObjVal! "result" (toJson "success")))) "unexecuted build cannot masquerade as success"

/-- Candidate-state regressions exercise the same pure update used by production evidence lookup. -/
def selfTestCandidate (count : IO.Ref Nat) : IO Unit := do
  let priorAccepted := Json.mkObj [("registry",toJson (1 : Nat))]
  expect count (settleCandidate priorAccepted (.error ()) == (priorAccepted,false))
    "candidate exception retains accepted readers and stops remaining effects"
  expect count (settleCandidate priorAccepted (.ok priorAccepted) == (priorAccepted,true))
    "candidate mismatch skips only its reader and continues"

/-- Reader closure and compiler-input counterfactuals stay separate from producer transport tests. -/
def selfTestReaderClosures (root : System.FilePath) (count : IO.Ref Nat) (envJson : Json)
    (cache : IO.Ref (Array (Nat × Loaded))) : IO Unit := do
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
      (!(Checker.Regressions.groups.any (fun group => group.name == name && group.corpus)))) "corpus copy closure and synthetic projection"
  let controlRows := rows.set! 0 ⟨"Checker/CheckAll.lean","100644","blob","new-control"⟩
  let (controlInputs,controlEngine) ← payloads root controlRows headers registryA policy (Json.mkObj []) envJson
  let (_,originalEngine) ← payloads root rows headers registryA policy (Json.mkObj []) envJson
  expect count (controlEngine != originalEngine && controlInputs == before) "global producer authenticity is separate from each actual reader closure"
  let (nativeInputs,_) ← payloads root (rows.push ⟨"Checker/Data.lean","100644","blob","data"⟩) headers registryA policy (Json.mkObj []) envJson
  expect count (nativeInputs.getObjValD "skeleton-pure" == before.getObjValD "skeleton-pure" && nativeInputs.getObjValD "registry" != before.getObjValD "registry") "native validators do not invalidate pure semantic cases"
  let (semanticInputs,_) ← payloads root (rows.push ⟨"Checker/SemanticDriver.lean","100644","blob","semantic"⟩) headers registryA policy (Json.mkObj []) envJson
  expect count (semanticInputs.getObjValD "skeleton-pure" != before.getObjValD "skeleton-pure" && semanticInputs.getObjValD "content" == before.getObjValD "content") "semantic readers are separate from content transitions"
  let compilerEnvironment := envJson.setObjVal! "native_compiler" (toJson "changed toolchain backend")
  let (compilerInputs, _) ← payloads root rows headers registryA policy (Json.mkObj []) compilerEnvironment
  expect count (suites.all fun (name, _) => before.getObjValD name != compilerInputs.getObjValD name) "native compiler identity changes every actual input"
  let imageEnvironment := envJson.setObjVal! "ImageVersion" (toJson "new image build label")
  let (imageInputs,_) ← payloads root rows headers registryA policy (Json.mkObj []) imageEnvironment
  expect count (imageInputs == before) "runner image build label is audit provenance rather than a reader input"
  for key in #["RUNNER_OS","RUNNER_ARCH","ImageOS","lean","lake","git","curl","libc"] do
    let (changedInputs,_) ← payloads root rows headers registryA policy (Json.mkObj [])
      (envJson.setObjVal! key (toJson "different required runtime"))
    expect count (suites.all fun (name,_) => changedInputs.getObjValD name != before.getObjValD name)
      ("required runtime identity changes every actual input: " ++ key)
  let changedRows := rows.set! 1 ⟨".gitignore", "100644", "blob", "changed"⟩
  let (changed, _) ← payloads root changedRows headers registryA policy (Json.mkObj []) envJson
  expect count ((before.getObjValD "skeleton-composed") != (changed.getObjValD "skeleton-composed")) "composed gitignore is executable fixture input"
  let changedHeaders := headers.setObjVal! "registry/claims.tsv" (toJson "new header")
  let (changed, _) ← payloads root rows changedHeaders registryA policy (Json.mkObj []) envJson
  expect count ((before.getObjValD "skeleton-composed") != (changed.getObjValD "skeleton-composed")) "composed registry schema closure"
  let transport := curlArguments "owner/repo" "/actions/jobs/11/logs"
  expect count (transport[0]! == "--disable" && transport.contains "--proto-redir" &&
    !transport.contains "--location-trusted" && !transport.any (fun x => (x.splitOn "Authorization").length > 1)) "curl configuration and credential boundary"
  let badToken : Evidence := ⟨"owner/repo", "invalid\ncredential", (← IO.monoMsNow) + 45000, "engine", cache⟩
  reject count (http root badToken "/actions/runs/7") "credential config injection rejected before HTTP"

/-- Fast negative and positive tests cover dispatch, schema, ancestry, scope and secrecy. -/
def selfTest (root : System.FilePath) : IO Unit := do
  let count ← IO.mkRef 0
  selfTestDiagnostics root count
  selfTestData root count
  selfTestInputs root count
  selfTestCandidate count
  expect count ((Json.mkObj [("z", toJson "last"), ("a", toJson "first")]).compress ==
    (Json.mkObj [("a", toJson "first"), ("z", toJson "last")]).compress) "canonical JSON key order"
  for status in #["A", "D", "T", "R100"] do
    expect count (changeForcesFull "README.md" status "100644" "100644" false) "all raw endpoints"
  for (path, oldMode, newMode, header) in #[
    ("unknown", "100644", "100644", false), ("registry/new.tsv", "100644", "100644", false),
    ("README.md", "100644", "100755", false), ("README.md", "100644", "120000", false),
    ("registry/claims.tsv", "100644", "100644", true),
    ("registry/bindings.tsv", "100644", "100644", true)] do
    expect count (changeForcesFull path "M" oldMode newMode header) "full fallback input"
  for path in #["Checker/CheckAll.lean","Checker/Inputs.lean","Checker/Tests/SkeletonPure.lean"] do
    expect count (!changeForcesFull path "M" "100644" "100644" false) "known reader changes do not veto unrelated groups"
  expect count (!changeForcesFull "registry/claims.tsv" "M" "100644" "100644" false) "known corpus edit"
  expect count (policyProjection "README.md" "exact PR exact head SHA prose" ==
    policyProjection "README.md" "different prose exact PR exact head SHA") "policy prose projection"
  expect count (policyProjection "README.md" "no gate" != policyProjection "README.md" "exact PR exact head SHA") "policy predicates"
  for (phase, rows, needed) in #[("bootstrap", 1, false), ("vocabulary", 1, true), ("census", 2, true)] do
    expect count ((currentPlan phase rows).contains "vocabulary" == needed) "semantic current selection"
  for mode in #["--current", "--full", "--ci", "--self-test"] do
    expect count ((options [mode] {}).isOk) "known CLI mode"
  for args in [[], ["--current", "--full"], ["--unknown"], ["--base"]] do
    expect count (!(options args {}).isOk) "invalid CLI rejected"
  validReceipt fixtureReceipt
  expect count true "valid receipt"
  reject count (validReceipt (fixtureReceipt.setObjVal! "version" (toJson (4 : Nat)))) "prior v4 has a different runtime input recipe"
  reject count (validReceipt (fixtureReceipt.setObjVal! "version" (toJson (2 : Nat)) )) "previous v2 receipt cannot be current evidence"
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
  let plan := (currentPlan "vocabulary" 3).map (fun action => (⟨action,#[]⟩ : Command)) ++
    suites.map (fun (name, _) => ⟨name,#[]⟩) ++ #[⟨"lake",#["build"]⟩]
  for target in [:plan.size] do
    let calls ← IO.mkRef 0
    reject count (execute (fun _ => do
      let index ← calls.get; calls.modify (·+1)
      require (index != target) "injected selected failure") plan) "every current/selected failure propagates"
    expect count ((← calls.get) == target + 1) "no commands after failed gate"
  let cache ← IO.mkRef #[]
  let e : Evidence := ⟨"owner/repo", "fixture", 0, "engine", cache⟩
  reject count (http root e "/actions/runs/7") "expired lookup does not contact network"
  reject count (output root "git" #["definitely-invalid-checker-command"]) "external exit is mandatory"
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
  expect count (← originalBound original origin "skeleton-pure" signature envJson) "direct executed original"
  let imageEnvironment := envJson.setObjVal! "ImageVersion" (toJson "different image build label")
  expect count (← candidateBound fixtureReceipt ctx source imageEnvironment) "image label alone preserves exact source-bound candidate"
  expect count (← originalBound original origin "skeleton-pure" signature imageEnvironment) "image label alone preserves directly executed origin"
  for key in #["RUNNER_OS","RUNNER_ARCH","ImageOS","lean","lake","git","curl","libc","native_compiler"] do
    let changedEnvironment := envJson.setObjVal! key (toJson "different required runtime")
    expect count (!(← candidateBound fixtureReceipt ctx source changedEnvironment)) ("candidate rejects required runtime change: " ++ key)
    expect count (!(← originalBound original origin "skeleton-pure" signature changedEnvironment)) ("origin rejects required runtime change: " ++ key)
  for key in #["run_attempt", "job_id"] do
    expect count (!(← originalBound original (origin.setObjVal! key (toJson (99 : Nat))) "skeleton-pure" signature envJson)) "original job or attempt mismatch"
  let recursive := fixtureReceipt.setObjVal! "suites" <|
    (fixtureReceipt.getObjValD "suites").setObjVal! "skeleton-pure" <| Json.mkObj [
      ("input", toJson signature), ("result", toJson "reused"), ("origin", origin)]
  expect count (!(← originalBound ⟨recursive, origin⟩ origin "skeleton-pure" signature envJson)) "recursive original rejected"
  expect count (!(← originalBound original origin "skeleton-pure" "other" envJson)) "original input mismatch"
  for label in #["API unavailable", "historical fixture unavailable"] do
    let selected ← orFull (throw <| IO.userError label)
    expect count (suites.all fun (name, _) => regressionRequired "--ci" selected.accepted name) "lookup and history failure require all suites"
  let allAccepted := Json.mkObj (suites.toList.map fun (name, _) => (name, origin))
  expect count (suites.all fun (name, _) => !regressionRequired "--current" allAccepted name) "current coverage stays partial"
  expect count (suites.all fun (name, _) => regressionRequired "--full" allAccepted name) "explicit full cannot reuse"
  selfTestReaderClosures root count envJson cache
  IO.println s!"check-all self-test: {(← count.get)} positive/negative assertions passed"

/-- Describe each decision before any gate runs; skipped work is never reported as executed. -/
def printPlan (mode : String) (selection : Selection) : IO Unit := do
  IO.println s!"check-all: receipt recipe v{version}; maximum 2 independent regression children"
  IO.println "check-all: fresh current native data, required semantic imports, generator and actual transition"
  for (name,_) in suites do
    let origin := selection.accepted.getObjValD name
    if mode == "--current" then IO.println s!"check-all: plan {name}: not_selected (current-only mode)"
    else if mode == "--full" || origin.isNull then IO.println s!"check-all: plan {name}: run ({selection.reason})"
    else IO.println s!"check-all: plan {name}: reuse (exact reader inputs, successful run {← nat origin "run_id"}, job {← nat origin "job_id"})"
  IO.println s!"check-all: plan mathematical build: {if selection.build.required then "run" else "not_required"} ({selection.build.reason})"

/-- Measure one existing verification phase, including failures, without affecting its acceptance result. -/
def timed (label : String) (operation : IO α) : IO α := do
  let started ← IO.monoMsNow
  try operation
  finally IO.println s!"check-all timing: {label} elapsed_ms={(← IO.monoMsNow)-started}"

/-- Bind the immutable CI checkout, live index and canonical executable before and after child execution. -/
def regressionFingerprint (root executable : System.FilePath) (expected : Json) : IO Json := do
  let actual ← context root
  require (actual == expected) "verification checkout changed during execution"
  return Json.mkObj [("checkout",actual),
    ("index",toJson (← digest root (toJson (← git root #["ls-files","--stage","-z"])))),
    ("executable",toJson (← toolDigest root executable))]

/-- Fresh current gates precede bounded isolated regression children; only fully joined success produces evidence. -/
def dispatch (root : System.FilePath) (o : Options) : IO Unit := do
  if o.mode == "--self-test" then timed "control-self-test" (selfTest root); return
  let (ctx,base,selection) ← if o.mode == "--ci" then do
    validateOverrides root
    let ctx ← context root
    let base ← str ctx "base"
    let full ← fullRequired root base (← str ctx "head")
    let selection ← orFull (calculateSelection root ctx full)
    pure (ctx,base,selection)
    else do
      let base ← commit root o.base
      let selection : Selection := {build := ← selectLocalBuild root base (← commit root "HEAD")}
      pure (Json.null,base,selection)
  printPlan o.mode selection
  timed "control-self-test" (selfTest root)
  let current ← timed "native-data" (currentData root)
  if o.mode == "--ci" then
    timed "semantic-import-cache" <| prepareImports root current
      (suites.filterMap fun (name,_) => if regressionRequired o.mode selection.accepted name then some name else none)
  let actions := (currentPlan (Registry.phase current) (current.table "modules").records.size).map fun action => (⟨action,#[]⟩ : Command)
  execute (fun action => do
    IO.println s!"check-all: current {action.cmd}"
    timed ("current:" ++ action.cmd) (currentAction root base action.cmd)) actions
  let executable ← IO.FS.realPath (← IO.appPath)
  if o.mode != "--current" then
    require (executable == (← IO.FS.realPath (root / ".lake/build/bin/checker")))
      "regressions require the canonical project-native checker"
  let frozen ← if o.mode == "--ci" then some <$> regressionFingerprint root executable ctx else pure none
  let results ← if o.mode == "--current" then pure (Json.mkObj []) else
    do
    let selected := suites.filterMap fun (name,_) =>
      if regressionRequired o.mode selection.accepted name then some name else none
    timed "selected-regressions" <| Checker.RegressionPool.runRegressionGroups root executable selected
    suites.foldlM (fun results (name,_) => do
      let accepted := if o.mode == "--full" then Json.null else selection.accepted.getObjValD name
      if accepted.isNull then
        IO.println s!"check-all: completed regression {name}"
      else IO.println s!"check-all: reused regression {name}"
      return results.setObjVal! name <| Json.mkObj [
        ("input",selection.sigs.getObjValD name),
        ("result",toJson (if accepted.isNull then "executed" else "reused")),("origin",accepted)]) (Json.mkObj [])
  if selection.build.required then timed "mathematical-build" (runGate root ⟨"lake",#["build"]⟩)
  else IO.println s!"check-all: mathematical build not_required: {selection.build.reason}"
  if let some frozen := frozen then
    require ((← regressionFingerprint root executable ctx) == frozen)
      "verification index or executable changed during regression execution"
  if o.mode == "--ci" && !selection.sigs.isNull && !selection.runtime.isNull && !selection.executable.isEmpty then
    let build := Json.mkObj [
      ("result",toJson (if selection.build.required then "executed" else "not_required")),
      ("reason",toJson selection.build.reason),("before",toJson selection.build.before),("after",toJson selection.build.after),
      ("origin",if selection.build.required then Json.null else selection.buildOrigin)]
    let receipt := ctx.mergeObj <| Json.mkObj [("version",toJson version),
      ("run_id",toJson ((← env "GITHUB_RUN_ID").toNat!)),("run_attempt",toJson ((← env "GITHUB_RUN_ATTEMPT").toNat!)),
      ("engine",toJson selection.executable),("environment",selection.runtime),("suites",results),
      ("current",toJson "success"),("transition",toJson "success"),("build",build)]
    validReceipt receipt
    IO.println (marker ++ receipt.compress)
  IO.println (if o.mode == "--current" then "check-all: current gates passed; regression acceptance remains required in CI"
    else "check-all: all selected gates passed")

end Checker.CheckAll
