import Checker.TestSupport

/-! Closed-tree, fixture-boundary and phase-aware policy regression cases. -/
namespace Checker.Tests.TreePolicy
open System Checker.TestSupport

/-- Write one owned fixture file, creating only its containing directories. -/
def write (path : FilePath) (text : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

/-- The byte-exact declaration-free root is an immutable policy input. -/
def canonicalRoot : String :=
  "/-!\n# LatticeSystem\n\nEmpty production root for the from-scratch Tasaki formalization.\nNo theorem declarations, imports, commands, or notation exist here.\n-/\n"

/-- Construct a synthetic policy dataset without borrowing a repository's current status. -/
def policyCase (ctx : Context) (name phase : String) (vocabulary : Bool := false) : IO FilePath := do
  let root := ctx.temporary / name
  write (root / "registry/phase.tsv") ("phase\n" ++ phase ++ "\n")
  let gate := "The exact PR and exact head SHA are required.\n"
  write (root / "README.md") gate; write (root / "DESIGN.md") gate
  write (root / ".github/pull_request_template.md") (gate ++ "\n- [ ] USER ONLY\n")
  let rootText ← if vocabulary then IO.FS.readFile (ctx.project / "LatticeSystem.lean") else pure canonicalRoot
  write (root / "LatticeSystem.lean") rootText
  return root

/-- Stage only this fixture's explicitly enumerated files, never a parent worktree or dependency tree. -/
partial def fixtureFiles (root : FilePath) (relative : String := "") : IO (Array String) := do
  let mut result := #[]
  for entry in ← (root / relative).readDir do
    if entry.fileName == ".git" then continue
    let child := if relative.isEmpty then entry.fileName else relative ++ "/" ++ entry.fileName
    let metadata ← entry.path.symlinkMetadata
    if metadata.type == .dir then result := result ++ (← fixtureFiles root child)
    else result := result.push child
  return result

/-- Policy lexical hygiene requires an actual Git index in the isolated fixture. -/
def policyRepo (root : FilePath) : IO Unit := do
  discard <| git root #["init","--quiet"]
  let files ← fixtureFiles root
  discard <| git root (#["add","--"] ++ files)

/-- Build one registered-statement policy fixture and its real tracked file set. -/
def skeletonCase (ctx : Context) (name registered vocabulary : String)
    (claim : String := "theorem stub : True := by sorry") : IO FilePath := do
  let root ← policyCase ctx name "skeleton" true
  writeTable root "statement-modules.tsv" <| #[#["module","source_path","role"]] ++
    (if registered == "none" then #[] else #[#[((registered.dropSuffix ".lean").toString.replace "/" "."),registered,"leaf"]])
  write (root / "LatticeSystem/Vocabulary/Quantum.lean") ("/-! Vocabulary fixture. -/\n" ++ vocabulary ++ "\n")
  write (root / "LatticeSystem/Claims/Front.lean") ("/-! Claim fixture. -/\n" ++ claim ++ "\n")
  write (root / "LatticeSystem/Claims/Other.lean") "/-! Second claim fixture. -/\n"
  policyRepo root
  return root

/-- Run all former tree-policy fixtures, including Git-index and external-root counterfactuals. -/
def run (ctx : Context) : IO Unit := do
  let makeTree := fun name paths => do
    let root := ctx.temporary / name
    write (root / "tracked-files.txt") (String.intercalate "\n" paths ++ "\n")
    pure root
  let fake ← makeTree "tree-fake-bypass" ["README.md"]
  let unexpected ← makeTree "tree-unexpected" ["README.md","unexpected.txt"]
  let unlisted ← makeTree "tree-unlisted" ["fixtures/tree-ghost/tracked-files.txt"]
  discard <| expect ctx "fake-tracked-files-bypass" false (ctx.gate "tree" fake)
  let treeFixture := fun target => {ctx.gate "tree" target with args := #["--gate","tree","--fixture",target.toString]}
  discard <| expect ctx "unexpected-path" false (treeFixture unexpected)
  discard <| expect ctx "unlisted-fixture" false (treeFixture unlisted)
  let rootOverride := fun command value => {command with env := command.env.push ("LATTICE_TEST_ROOT",some value)}
  discard <| expect ctx "fixture-root-repository-reject" false
    (rootOverride (treeFixture ctx.project) ctx.project.toString) "must be repository-external"
  discard <| expect ctx "fixture-root-ancestor-census-reject" false
    (rootOverride {ctx.gate "census" unexpected with args := #["--gate","census","--fixture",unexpected.toString]} "/")
    "must not contain the repository"
  discard <| expect ctx "fixture-root-ancestor-vocabulary-reject" false
    (rootOverride (ctx.command "vocabulary" #["--fixture",unexpected.toString]) "/") "must not contain the repository"
  discard <| expect ctx "fixture-root-ancestor-base-diff-reject" false
    (rootOverride (ctx.command "base-diff" #["--fixture-dirs",fake.toString,unexpected.toString]) "/")
    "must not contain the repository"
  let forbidden ← policyCase ctx "policy-forbidden" "bootstrap"
  write (forbidden / "LatticeSystem.lean") "/-! Forbidden-token fixture. -/\naxiom escapedProof : True\n"
  let check ← policyCase ctx "policy-root-check" "bootstrap"
  write (check / "LatticeSystem.lean") (canonicalRoot ++ "#check True\n")
  let comments ← policyCase ctx "policy-comment-allowed" "bootstrap"
  let missing ← policyCase ctx "policy-merge-missing" "bootstrap"
  write (missing / "DESIGN.md") "This fixture intentionally omits the merge authorization wording.\n"
  let checkedGate ← policyCase ctx "policy-merge-checked" "bootstrap"
  write (checkedGate / ".github/pull_request_template.md") "The exact PR and exact head SHA are required.\n\n- [x] USER ONLY\n"
  let census ← policyCase ctx "policy-phase-advance" "census"
  let future ← policyCase ctx "policy-future-phase" "vocabulary" true
  discard <| expect ctx "vocabulary-policy-missing-index" false (ctx.gate "policy" future) "external operation failed: git"
  policyRepo future
  let front := "LatticeSystem/Claims/Front.lean"
  let good ← skeletonCase ctx "policy-skeleton-good" front "def quantumDimension : Nat := 2"
  let empty ← skeletonCase ctx "policy-skeleton-empty" "none" "def quantumDimension : Nat := 2"
  let unregistered ← skeletonCase ctx "policy-skeleton-unregistered" "LatticeSystem/Claims/Other.lean" "def quantumDimension : Nat := 2"
  let hygiene ← skeletonCase ctx "policy-skeleton-hygiene" front "theorem leaked : True := trivial"
  let axiomCase ← skeletonCase ctx "policy-skeleton-axiom" front "def quantumDimension : Nat := 2" "axiom interfaceAxiom : True"
  let native ← skeletonCase ctx "policy-skeleton-native" front "def quantumDimension : Nat := 2" "theorem stub : True := by native_decide"
  let admit ← skeletonCase ctx "policy-skeleton-admit" front "def quantumDimension : Nat := 2" "theorem stub : True := by admit"
  let dual ← skeletonCase ctx "policy-skeleton-dual" front "def quantumDimension : Nat := 2" "theorem sneaky : True := trivial"
  writeTable dual "modules.tsv" #[#["module","source_path","role"],#["LatticeSystem.Claims.Front",front,"leaf"]]
  policyRepo dual
  for (label,root,positive,needle) in #[
    ("skeleton-policy",good,true,""),
    ("skeleton-policy-no-statement-modules",empty,false,"skeleton phase requires registered statement modules"),
    ("skeleton-policy-unregistered-statement",unregistered,false,"forbidden token (nonsemantic check): LatticeSystem/Claims/Front.lean"),
    ("skeleton-policy-hygiene",hygiene,false,"forbidden token (nonsemantic check): LatticeSystem/Vocabulary/Quantum.lean"),
    ("skeleton-policy-registered-axiom",axiomCase,true,""),
    ("skeleton-policy-native-decide",native,false,"forbidden token (nonsemantic check): LatticeSystem/Claims/Front.lean"),
    ("skeleton-policy-admit",admit,false,"forbidden token (nonsemantic check): LatticeSystem/Claims/Front.lean"),
    ("skeleton-policy-dual-registration",dual,false,"registered as both a vocabulary and a statement module"),
    ("forbidden-token",forbidden,false,""),("root-check",check,false,""),
    ("comment-theorem-allowed",comments,true,""),("merge-gate-missing",missing,false,""),
    ("merge-gate-checked",checkedGate,false,""),("census-phase",census,true,""),("vocabulary-policy",future,true,"") ] do
    discard <| expect ctx label positive (ctx.gate "policy" root) needle
  IO.println "test-tree-policy: ok"

end Checker.Tests.TreePolicy
