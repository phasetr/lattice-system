import Checker.TestSupport

/-! Typed fixture mutations shared by registry, transition and semantic regression groups. -/
namespace Checker.Tests.Fixtures
open System Checker.TestSupport

/-- Rewrite a fixture's explicit relative TSV path, including historical reference tables. -/
def editFile (root : FilePath) (relative : String)
    (change : Nat → Array String → Option (Array String)) : IO Unit := do
  let path := root / relative
  let records := rowsOf (← IO.FS.readFile path)
  let changed := (records.zipIdx).filterMap fun (row,index) => change (index+1) row
  IO.FS.writeFile path (String.join (changed.toList.map fun row => String.intercalate "\t" row.toList ++ "\n"))

/-- Transform physical TSV data records with explicit one-based file record numbers. -/
def rewrite (root : FilePath) (name : String)
    (change : Nat → Array String → Option (Array String)) : IO Unit := do
  let rows ← table root name
  writeTable root name ((rows.zipIdx).filterMap fun (row,index) => change (index+1) row)

/-- Apply explicit zero-based field replacements to a physical record. -/
def setFields (row : Array String) (fields : Array (Nat × String)) : Array String :=
  fields.foldl (fun row (index,value) => row.set! index value) row

/-- Change named columns in one physical TSV record and preserve every other record. -/
def mutateLine (root : FilePath) (name : String) (line : Nat) (fields : Array (Nat × String)) : IO Unit :=
  rewrite root name fun index row => some (if index == line then setFields row fields else row)

/-- Explicitly retain only a schema header, without treating an absent file as an empty table. -/
def headerOnly (root : FilePath) (name : String) : IO Unit :=
  rewrite root name fun index row => if index == 1 then some row else none

/-- Replace a fixture table using a quoted single-line row representation, never a program string. -/
def replace (root : FilePath) (name : String) (records : Array String) : IO Unit :=
  writeTable root name (records.map fun row => (row.splitOn "\t").toArray)

/-- Append one literal TSV record, using the old AWK-plus-printf LF normalization contract. -/
def add (root : FilePath) (name row : String) : IO Unit := do
  writeTable root name ((← table root name).push (row.splitOn "\t").toArray)

/-- Write an explicit file under an owned fixture, including its exact terminal bytes. -/
def write (root : FilePath) (relative text : String) : IO Unit := do
  let path := root / relative
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

/-- Exact baseline-file identity for the immutable common-corpus oracle. -/
def fingerprint (ctx : Context) (root : FilePath) : IO String := do
  let entries := (← (root / "registry").readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut text := ""
  for entry in entries do
    if (← entry.path.symlinkMetadata).type == .file then
      let oid := (← git ctx.project #["hash-object",entry.path.toString]).trimAscii.toString
      text := text ++ entry.fileName ++ "\x00" ++ oid ++ "\n"
  blob ctx text

/-- Read the immutable tracked baseline without creating a checkout or copying private files. -/
def cloneCommitRegistry (ctx : Context) (commit : String) (target : FilePath) : IO Unit := do
  newTarget ctx target
  let paths ← git ctx.project #["ls-tree","-r","-z","--name-only",commit,"registry"]
  for relative in paths.splitOn "\x00" do
    unless relative.isEmpty do
      ensure (relative.startsWith "registry/" && !(relative.splitOn "/").contains "..") "unsafe historical fixture path"
      write target relative (← git ctx.project #["show",commit ++ ":" ++ relative])

end Checker.Tests.Fixtures
