import Lean

/-! Job-local tool preparation using verified official release assets and the declared dependency pin.
This module deliberately depends only on the Lean distribution which launches it.
-/
namespace Checker.Bootstrap
open Lean System

/-- Stop with a bounded diagnostic rather than exposing subprocess arguments or response bodies. -/
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

/-- Remove command terminators without interpreting a captured response. -/
private def trim (text : String) : String := text.trimAscii.toString

/-- Only the exact declared release supported by the verified first-stage launcher can proceed. -/
private def supportedToolchain : String := "leanprover/lean4:v4.29.0"

/-- Execute a thin operation; no subprocess stderr, argv or secret-bearing environment is printed. -/
private def run (label command : String) (args : Array String := #[])
    (cwd : Option FilePath := none) (env : Array (String × Option String) := #[]) : IO String := do
  let result ← try
    IO.Process.output {cmd := command,args,cwd,env}
  catch _ => throw <| IO.userError ("Tool preparation command failed: " ++ label)
  require (result.exitCode == 0) ("Tool preparation command failed: " ++ label)
  return trim result.stdout

/-- An environment path must be explicitly supplied by the runner. -/
private def envPath (name : String) : IO FilePath := do
  let some value ← IO.getEnv name | throw <| IO.userError ("Missing runner environment: " ++ name)
  require (!value.isEmpty) ("Missing runner environment: " ++ name)
  return FilePath.mk value

/-- The only removable owner is a canonical, named immediate child of the canonical runner temp root. -/
private def owner (path : FilePath) : IO FilePath := do
  let runner ← IO.FS.realPath (← envPath "RUNNER_TEMP")
  let root ← IO.FS.realPath path
  require (root.parent == some runner && (root.fileName.getD "").startsWith "rewrite-ci-tools-")
    "Refusing unexpected cleanup path"
  require ((← root.symlinkMetadata).type == .dir) "Tool root is not a directory"
  return root

/-- Append runner command-file records without a shell or global environment mutation. -/
private def appendEnvironment (name text : String) : IO Unit := do
  let path ← envPath name
  IO.FS.withFile path .append fun handle => handle.putStr text

/-- Fixed request roles identify failures without revealing URLs or captured HTTP data. -/
private inductive Request where
  | mathlibSource | elanRelease | leanRelease | leantarRelease | elanAsset | leantarAsset

/-- Only source-owned labels can appear in a request diagnostic. -/
private def Request.label : Request → String
  | .mathlibSource => "pinned-mathlib-source"
  | .elanRelease => "elan-release-metadata"
  | .leanRelease => "lean-release-metadata"
  | .leantarRelease => "leantar-release-metadata"
  | .elanAsset => "elan-official-asset"
  | .leantarAsset => "leantar-official-asset"

/-- Accept exactly curl's three ASCII status digits, never arbitrary captured output. -/
private def httpStatus (output : String) : String :=
  let code := trim output
  if code.length == 3 && code.toList.all (fun c => '0' ≤ c && c ≤ '9') then code
  else "unavailable"

/-- Process-launch failure remains distinct from curl's HTTP 000 and transport exit statuses. -/
private def requestFailure (request : Request) (result : Option IO.Process.Output) : String :=
  let status := match result with
    | some result => s!"curl_exit={result.exitCode} http={httpStatus result.stdout}"
    | none => "curl_exit=unavailable http=unavailable"
  s!"Official asset request failed: {request.label} {status}"

/-- Only the exact GitHub repository API origin receives the job credential through stdin. -/
private def credentialConfig (url : String) (token : Option String) : Except String (Option String) := do
  if !url.startsWith "https://api.github.com/repos/" then return none
  let some token := token | throw "Missing bootstrap API credential"
  if token.isEmpty || !token.toList.all (fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\') then
    throw "Invalid bootstrap API credential encoding"
  return some s!"header = \"Authorization: Bearer {token}\"\n"

/-- Curl retains HTTPS-only, credential-stripping redirects and never receives token bytes in argv. -/
private def requestArguments (url : String) (target : FilePath) (binary authenticated : Bool) : Array String :=
  #["--disable","--fail","--location","--silent","--show-error",
    "--proto","=https","--proto-redir","=https","--connect-timeout","10","--max-time",
    if binary then "300" else "30","--output",target.toString,"--write-out","%{http_code}"] ++
    (if binary then #["--header","Accept: application/octet-stream"] else #[]) ++
    (if authenticated then #["--config","-"] else #[]) ++ #[url]

/-- Fetch official HTTPS data, discarding failed bodies and retaining the three-attempt retry budget. -/
private def get (request : Request) (url : String) (target : FilePath) (binary : Bool := false) : IO Unit := do
  let config ← IO.ofExcept (credentialConfig url (← IO.getEnv "GH_TOKEN"))
  for attempt in [:3] do
    if ← target.pathExists then IO.FS.removeFile target
    let args := requestArguments url target binary config.isSome
    let result ← try
      pure (some (← IO.Process.output {cmd := "curl",args} config))
    catch _ => pure none
    if result.any (fun output => output.exitCode == 0) then return
    let message := requestFailure request result
    if attempt == 2 then
      if ← target.pathExists then IO.FS.removeFile target
      throw <| IO.userError (message ++ " after 3 attempts")
    IO.eprintln (message ++ s!" (attempt {attempt+1}/3)")
    IO.sleep 5000

/-- Decode JSON without ever echoing an untrusted HTTP body. -/
private def readJson (path : FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .ok value => pure value
  | .error _ => throw <| IO.userError "Invalid official JSON metadata"

/-- Missing or incorrectly typed metadata fields produce bounded diagnostics. -/
private def field (value : Json) (name : String) : IO Json :=
  match value.getObjVal? name with
  | .ok result => pure result
  | .error _ => throw <| IO.userError ("Missing official metadata field: " ++ name)

/-- Read a required string without exposing unexpected metadata contents. -/
private def stringField (value : Json) (name : String) : IO String := do
  match (← field value name).getStr? with
  | .ok result => pure result
  | .error _ => throw <| IO.userError ("Invalid official metadata field: " ++ name)

/-- Read the positive integer fields which identify a release asset and its exact byte size. -/
private def positiveField (value : Json) (name : String) : IO Nat := do
  let number ← match (← field value name).getNat? with
    | .ok number => pure number
    | .error _ => throw <| IO.userError "Invalid release asset ID or size"
  require (number > 0) "Invalid release asset ID or size"
  return number

/-- Reject Unicode, uppercase or truncated digests. -/
private def hex (value : String) (width : Nat) : Bool :=
  value.length == width && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

/-- The release protocol accepts exactly three nonempty ASCII decimal version components. -/
private def version (value : String) : Bool :=
  let parts := value.splitOn "."
  parts.length == 3 && parts.all fun part =>
    !part.isEmpty && part.toList.all (fun c => '0' ≤ c && c ≤ '9')

/-- Require stable, published release metadata and bind tagged requests to their exact declared version. -/
private def metadata (request : Request) (repo selector : String) (target : FilePath) : IO Json := do
  get request ("https://api.github.com/repos/" ++ repo ++ "/releases/" ++ selector) target
  let release ← readJson target
  let draft := release.getObjValAs? Bool "draft"
  let prerelease := release.getObjValAs? Bool "prerelease"
  require (draft.toOption == some false && prerelease.toOption == some false) "A stable published release is required"
  let tag ← stringField release "tag_name"
  require (tag.startsWith "v" && version (tag.drop 1).toString) "Unexpected release tag"
  if selector.startsWith "tags/" then
    require (tag == (selector.drop 5).toString) "Release tag differs from the declared version"
  return release

/-- The unique official asset identity includes its API URL, browser URL, size and SHA256 digest. -/
private structure Asset where
  url : String
  size : Nat
  digest : String
  tag : String

/-- A release asset cannot be selected by a lookalike name, alternate URL or unverified digest. -/
private def assetMetadata (repo : String) (release : Json) (name : String) : IO Asset := do
  let assets ← match release.getObjValAs? (Array Json) "assets" with
    | .ok values => pure values
    | .error _ => pure #[]
  let selected := assets.filter fun asset => (asset.getObjValAs? String "name").toOption == some name
  require (selected.size == 1) ("Expected exactly one official asset: " ++ name)
  let item := selected[0]!
  let id ← positiveField item "id"
  let size ← positiveField item "size"
  let digest ← stringField item "digest"
  let tag ← stringField release "tag_name"
  let expectedUrl := s!"https://api.github.com/repos/{repo}/releases/assets/{id}"
  let expectedBrowser := s!"https://github.com/{repo}/releases/download/{tag}/{name}"
  let message := "Official asset identity or SHA256 metadata is invalid"
  require ((← stringField item "state") == "uploaded") message
  require ((← stringField item "url") == expectedUrl) message
  require ((← stringField item "browser_download_url") == expectedBrowser) message
  require (digest.startsWith "sha256:" && hex (digest.drop 7).toString 64) message
  return ⟨expectedUrl,size,(digest.drop 7).toString,tag⟩

/-- Verify whole archive bytes before any of its contents are extracted or executed. -/
private def verifyAsset (repo name : String) (asset : Asset) (target : FilePath) : IO Unit := do
  let stat ← target.symlinkMetadata
  require (stat.type == .file && stat.byteSize.toNat == asset.size)
    ("Asset size/SHA256 verification failed: " ++ name)
  let sum ← run "sha256sum" "sha256sum" #["--",target.toString]
  require ((sum.splitOn " ").head! == asset.digest) ("Asset size/SHA256 verification failed: " ++ name)
  IO.println s!"Verified official asset {repo}:{asset.tag}/{name}"

/-- Download and verify only official assets selected from the release metadata. -/
private def asset (request : Request) (repo : String) (release : Json) (name : String) (target : FilePath) : IO Unit := do
  let item ← assetMetadata repo release name
  get request item.url target true
  verifyAsset repo name item target

/-- Decode the Contents API body as bytes, retaining the original non-strict base64 decoding behavior. -/
private def decodeSource (encoded : String) (work : FilePath) : IO ByteArray := do
  let input := work / "mathlib-io.base64"
  IO.FS.writeFile input encoded
  let child ← try
    IO.Process.spawn {
      cmd := "base64"
      args := #["--decode","--ignore-garbage",input.toString]
      stdin := .null
      stdout := .piped
      stderr := .null }
  catch _ => throw <| IO.userError "Pinned Mathlib source base64 decoding failed"
  let pending ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let status ← child.wait
  let source ← IO.ofExcept pending.get
  require (status == 0) "Pinned Mathlib source base64 decoding failed"
  return source

/-- Bytes-mode regular-expression whitespace is ASCII, unlike registry-content Unicode strip. -/
private def byteSpace (byte : UInt8) : Bool := #[9,10,11,12,13,32].contains byte.toNat

/-- Scan only the available bytes, threading the position through a bounded pure recursion. -/
private def scanBytes (source : ByteArray) (predicate : UInt8 → Bool) : Nat → Nat → Nat
  | 0, position => position
  | fuel+1, position =>
    if (source[position]?).any predicate then scanBytes source predicate fuel (position+1) else position

/-- Match the original numeric dotted version after a particular LEANTARVERSION definition. -/
private def versionAt (source : ByteArray) (start : Nat) : Option String := do
  let first := scanBytes source byteSpace source.size start
  if source[first]? != some 58 || source[first+1]? != some 61 then none else do
    let quoted := scanBytes source byteSpace source.size (first+2)
    if source[quoted]? != some 34 then none else do
      let begin := quoted+1
      let digits := scanBytes source (fun byte => 48 ≤ byte && byte ≤ 57) source.size
      let endOne := digits begin
      if endOne == begin || source[endOne]? != some 46 then none else do
        let endTwo := digits (endOne+1)
        if endTwo == endOne+1 || source[endTwo]? != some 46 then none else do
          let endThree := digits (endTwo+1)
          if endThree == endTwo+1 || source[endThree]? != some 34 then none else
            String.fromUTF8? (source.extract begin endThree)

/-- Collect matches in source order without constructing a range-sized list or array. -/
private def matchingVersions (source marker : ByteArray) : Nat → Nat → Array String → Array String
  | 0, _, found => found
  | fuel+1, position, found =>
    let next := if source.extract position (position+marker.size) == marker then
      match versionAt source (position+marker.size) with
      | some value => found.push value
      | none => found
      else found
    matchingVersions source marker fuel (position+1) next

/-- Derive exactly one leantar version from the exact Contents API blob at the declared Mathlib commit. -/
private def leantarVersion (revision : String) (work : FilePath) : IO String := do
  let sourceMetadata := work / "mathlib-io.json"
  get .mathlibSource ("https://api.github.com/repos/leanprover-community/mathlib4/contents/Cache/IO.lean?ref=" ++ revision) sourceMetadata
  let data ← readJson sourceMetadata
  require ((← stringField data "encoding") == "base64") "Unexpected pinned Mathlib source encoding"
  let source ← decodeSource (← stringField data "content") work
  let path := work / "mathlib-io.lean"
  IO.FS.writeBinFile path source
  let gitEnv := #[("GIT_DIR",none),("GIT_WORK_TREE",none),("GIT_OBJECT_DIRECTORY",none),
    ("GIT_ALTERNATE_OBJECT_DIRECTORIES",none)]
  let actual ← run "Git blob verification" "git" #["hash-object","--no-filters",path.toString] (some work) gitEnv
  require (actual == (← stringField data "sha") && hex actual 40) "Pinned Mathlib source identity mismatch"
  let marker := "def LEANTARVERSION".toUTF8
  let versions := matchingVersions source marker source.size 0 #[]
  require (versions.size == 1) "Cannot identify the existing pinned leantar version"
  return versions[0]!

/-- Read the unchanged Mathlib dependency declaration, never substituting a branch or another repository. -/
private def mathlibRevision : IO String := do
  let manifest ← readJson "lake-manifest.json"
  let packages ← match (← field manifest "packages").getArr? with
    | .ok packages => pure packages
    | .error _ => throw <| IO.userError "Expected the existing declared Mathlib dependency"
  let selected := packages.filter (fun package => (package.getObjValAs? String "name").toOption == some "mathlib")
  require (selected.size == 1) "Expected the existing declared Mathlib dependency"
  let mathlib := selected[0]!
  require ((← stringField mathlib "url") == "https://github.com/leanprover-community/mathlib4")
    "Expected the existing declared Mathlib dependency"
  let revision ← stringField mathlib "rev"
  require (hex revision 40) "Mathlib must use its declared exact commit"
  return revision

/-- Bind this interpreter, its prefix and the immutable declaration to the verified first-stage Lean tree. -/
private def verifyInterpreter (root : FilePath) : IO Unit := do
  require ((← run "uname" "uname" #["-s"]) == "Linux" &&
    (← run "uname" "uname" #["-m"]) == "x86_64")
    "This workflow requires its existing x86_64 Linux runner"
  require (trim (← IO.FS.readFile "lean-toolchain") == supportedToolchain) "Unsupported declared Lean toolchain"
  let expected ← IO.FS.realPath (root / "lean/bin/lean")
  require ((← IO.FS.realPath (← IO.appPath)) == expected) "Bootstrap is not running the verified declared Lean interpreter"
  let actualPrefix ← run "Lean prefix verification" expected.toString #["--print-prefix"]
  require ((← IO.FS.realPath actualPrefix) == (← IO.FS.realPath (root / "lean")))
    "Lean prefix differs from the verified declared toolchain"
  let declared ← run "Lean version verification" expected.toString #["--version"]
  require (declared.startsWith "Lean (version 4.29.0,") "Prepared Lean version differs from the declared toolchain"

/-- Install only the verified job-local Elan/leantar assets and link the already verified Lean extraction. -/
private def install (root work : FilePath) (elanArchive leantarArchive : FilePath)
    (leantar : String) : IO Unit := do
  let elanHome := root / "elan"
  let leanRoot := root / "lean"
  let cache := root / "mathlib-cache"
  let installer := work / "elan-installer"
  for directory in #[installer,cache] do IO.FS.createDir directory
  let env := #[("ELAN_HOME",some elanHome.toString)]
  discard <| run "Elan archive extraction" "tar" #["-xzf",elanArchive.toString,"-C",installer.toString,"--no-same-owner"]
  discard <| run "Verified Elan installer" (installer / "elan-init").toString
    #["-y","--default-toolchain","none","--no-modify-path"] none env
  discard <| run "leantar archive extraction" "tar"
    #["-xzf",leantarArchive.toString,"-C",cache.toString,"--strip-components=1","--no-same-owner"]
  let leantarPath := cache / ("leantar-" ++ leantar)
  IO.FS.rename (cache / "leantar") leantarPath
  let elan := (elanHome / "bin/elan").toString
  discard <| run "Verified Elan toolchain link" elan #["toolchain","link",supportedToolchain,leanRoot.toString] none env
  let resolved ← run "Elan Lean resolution" elan #["which","lean"] none env
  require ((← IO.FS.realPath resolved) == (← IO.FS.realPath (leanRoot / "bin/lean")))
    "Elan does not resolve the verified declared toolchain"
  let path := (elanHome / "bin").toString ++ ":" ++ ((← IO.getEnv "PATH").getD "")
  let env := env.push ("PATH",some path)
  IO.println (← run "Prepared Lean version" "lean" #["--version"] none env)
  IO.println (← run "Prepared Lake version" "lake" #["--version"] none env)
  require ((← run "Prepared leantar version" leantarPath.toString #["--version"]) == "leantar " ++ leantar)
    "Prepared leantar version differs from the pinned Mathlib requirement"

/-- Continue the verified first stage; every remaining archive is authenticated before installer execution. -/
def prepare (ownedRoot : FilePath) : IO Unit := do
  let root ← owner ownedRoot
  verifyInterpreter root
  let revision ← mathlibRevision
  let elanHome := root / "elan"
  let cache := root / "mathlib-cache"
  appendEnvironment "GITHUB_ENV" s!"ELAN_HOME={elanHome}\nMATHLIB_CACHE_DIR={cache}\n"
  let work := root / "downloads"
  require (!(← work.pathExists)) "Tool downloads directory already exists"
  IO.FS.createDir work
  try
    let leantar ← leantarVersion revision work
    let elanRelease ← metadata .elanRelease "leanprover/elan" "latest" (work / "elan.json")
    let leanRelease ← metadata .leanRelease "leanprover/lean4" "tags/v4.29.0" (work / "lean.json")
    let leantarRelease ← metadata .leantarRelease "digama0/leangz" ("tags/v" ++ leantar) (work / "leantar.json")
    let elanArchive := work / "elan.tar.gz"
    let leantarArchive := work / "leantar.tar.gz"
    asset .elanAsset "leanprover/elan" elanRelease "elan-x86_64-unknown-linux-gnu.tar.gz" elanArchive
    let leanAsset ← assetMetadata "leanprover/lean4" leanRelease "lean-4.29.0-linux.tar.zst"
    verifyAsset "leanprover/lean4" "lean-4.29.0-linux.tar.zst" leanAsset (root / "lean.tar.zst")
    asset .leantarAsset "digama0/leangz" leantarRelease ("leantar-v" ++ leantar ++ "-x86_64-unknown-linux-musl.tar.gz") leantarArchive
    install root work elanArchive leantarArchive leantar
  finally
    let current ← owner root
    require (current == root && (← IO.FS.realPath work) == work &&
      (← work.symlinkMetadata).type == .dir) "Refusing unexpected downloads cleanup path"
    IO.FS.removeDirAll work
  appendEnvironment "GITHUB_PATH" ((elanHome / "bin").toString ++ "\n")

/-- Remove only the registered canonical job-local tool owner; symlink children are never followed. -/
def cleanup : IO Unit := do
  if let some tools ← IO.getEnv "REWRITE_CI_TOOLS" then
    let root ← owner (FilePath.mk tools)
    IO.FS.removeDirAll root

/-- The standalone stage has only an explicit owned-root preparation mode and environment-owned cleanup. -/
def dispatch (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--prepare",root] => prepare (FilePath.mk root)
    | ["--cleanup"] => cleanup
    | _ => throw <| IO.userError "usage: Bootstrap --prepare OWNED_ROOT | --cleanup"
    return 0
  catch error =>
    IO.eprintln s!"bootstrap: {error}"
    return 1

end Checker.Bootstrap

/-- Run the source-only bootstrap without a project build or any non-distribution Lean imports. -/
def main (args : List String) : IO UInt32 := Checker.Bootstrap.dispatch args
