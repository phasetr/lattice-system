import Checker.Support

/-! Explicit Git ancestry and immutable registry materialization for transition checks. -/
namespace Checker.History
open System Checker.CheckAll

/-- Resolve the actual repository top and independently verified merge base. -/
def actualBase (root : FilePath) (baseRef : String) : IO (FilePath × String) := do
  let root ← IO.FS.realPath root
  require (trim (← git root #["rev-parse","--show-toplevel"]) == root.toString) "ROOT must be the repository top"
  let baseTip ← try pure (trim (← git root #["rev-parse","--verify",baseRef ++ "^{commit}"]))
    catch _ => throw <| IO.userError s!"invalid or unfetched base ref: {baseRef}"
  let base ← try pure (trim (← git root #["merge-base","HEAD",baseTip]))
    catch _ => throw <| IO.userError s!"base ref has no merge base: {baseRef}"
  discard <| git root #["merge-base","--is-ancestor",base,"HEAD"]
  discard <| git root #["merge-base","--is-ancestor",base,baseTip]
  return (root,base)


/-- Materialize only tracked registry/reference bytes from one immutable source revision. -/
def materialize (repository : FilePath) (base : String) (target : FilePath) : IO Unit := do
  let paths ← git repository #["ls-tree","-r","-z","--name-only",base,"registry","references"]
  for path in split paths "\x00" do
    unless path.isEmpty do
      require ((path.startsWith "registry/" || path.startsWith "references/") &&
        !(path.splitOn "/").contains ".." && !path.startsWith "/") "unsafe historical registry path"
      let destination := target / path
      if let some parent := destination.parent then IO.FS.createDirAll parent
      IO.FS.writeFile destination (← git repository #["show",base ++ ":" ++ path])


/-- A successful exact-path Git inventory distinguishes true absence from an operation failure. -/
def hasPath (root : FilePath) (revision path : String) : IO Bool := do
  let paths ← git root #["ls-tree","-r","-z","--name-only",revision,"--",path]
  return (split paths "\x00").contains path


end Checker.History
