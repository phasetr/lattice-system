import Checker.Text
import Checker.Support

/-! The publication reader preserves the standard quoted TSV contract independently of native data gates. -/
namespace Checker.Publication
open Lean System Checker.CheckAll

/-- Publication rows retain missing CSV values as JSON null rather than inventing text. -/
abbrev Row := Json

/-- The exact fourteen public input schemas, in their original loading order. -/
def headers : Array (String × Array String) := #[
  ("tracks",#["track_id","position","title","public_slug"]),
  ("sources",#["source_id","track_id","source_position","source_kind","citation_key","title","authors","year","edition","identifier_kind","identifier","public_url","public_slug","local_ref_key","pdf_oid","text_oid","coverage"]),
  ("source_progress",#["source_id","lifecycle","review_ref"]),
  ("pages",#["page_id","source_id","order_key","printed_page","pdf_page","section","page_kind","pass1","pass2","source_oid"]),
  ("claims",#["claim_id","source_id","order_key","page_id","locator","disposition","subkind","normalized_content","content_oid","exclusion_rationale","exclusion_review_ref","tombstone","superseded_by","tombstone_rationale","tombstone_review_ref"]),
  ("source_items",#["item_id","source_id","order_key","page_id","item_kind","source_label","title","locator","public_group","public_slug","review_ref"]),
  ("item_claims",#["item_id","position","claim_id"]),
  ("claim_vocabulary_review",#["claim_id","basis","review_ref"]),
  ("vocabulary",#["vocabulary_id","declaration","module","declaration_kind","origin","parent_vocabulary_id","type_oid","declaration_oid","design_role","finiteness_scope"]),
  ("claim_vocabulary",#["claim_id","vocabulary_id"]),
  ("bindings",#["claim_id","statement_decl","proof_decl","module","statement_kind","statement_shape","statement_type_oid","statement_value_oid","implementation_status","proof_kind","proof_type_oid","proof_value_oid","nonvacuity_decl","nonvacuity_oid","review_ref"]),
  ("axioms",#["axiom_id","declaration","module","category","source_locator","rationale","reopen_condition","axiom_type_oid"]),
  ("claim_axioms",#["claim_id","axiom_id"]),
  ("phase",#["phase"])]

/-- Decode standard non-strict quoted TSV, including quoted tabs/newlines and missing fields. -/
def csvRows (text : String) : Array (Array String) := Id.run do
  let chars := text.toList.toArray
  let mut i := 0; let mut result := #[]; let mut row := #[]
  let mut value := ""; let mut quoted := false; let mut atStart := true; let mut touched := false
  while i < chars.size do
    let c := chars[i]!
    if quoted then
      if c == '"' then
        if chars[i+1]? == some '"' then value := value.push '"'; i := i+2
        else quoted := false; i := i+1
      else value := value.push c; i := i+1
    else if c == '"' && atStart then
      quoted := true; touched := true; atStart := false; i := i+1
    else if c == '\t' then
      row := row.push value; value := ""; atStart := true; touched := true; i := i+1
    else if c == '\n' || c == '\r' then
      result := result.push (if touched || !row.isEmpty || !value.isEmpty then row.push value else #[])
      row := #[]; value := ""; atStart := true; touched := false
      i := i + (if c == '\r' && chars[i+1]? == some '\n' then 2 else 1)
    else
      value := value.push c; touched := true; atStart := false; i := i+1
  if touched || !row.isEmpty || !value.isEmpty then result := result.push (row.push value)
  return result

/-- Read one known public schema; blank data records follow DictReader's skipped-row behavior. -/
def readTsv (path : FilePath) (expected : Array String) : IO (Array Row) := do
  let parsed := csvRows (← IO.FS.readFile path)
  require (parsed[0]? == some expected) s!"bad header for {path}"
  return (parsed.extract 1 parsed.size).filterMap fun values =>
    if values.isEmpty then none else some <| Json.mkObj <| (expected.zipIdx).toList.map fun (key,i) =>
      (key,(values[i]?).map toJson |>.getD Json.null)

/-- Encode one standard TSV field with exactly the delimiter/newline/quote escaping rules. -/
def csvField (text : String) : String :=
  if text.toList.any (fun c => c == '\t' || c == '\n' || c == '"') then
    "\"" ++ text.replace "\"" "\"\"" ++ "\""
  else text

/-- Write a canonical quoted TSV fixture without changing its field order. -/
def writeTsv (path : FilePath) (header : Array String) (rows : Array Row) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  let mut records := #[header]
  for row in rows do
    let values ← header.mapM fun key => do
      let value ← field row key
      if value.isNull then pure "" else IO.ofExcept value.getStr?
    records := records.push values
  IO.FS.writeFile path (String.join <| records.toList.map fun row =>
    String.intercalate "\t" (row.toList.map csvField) ++ "\n")

/-- Resolve one schema by its public logical name. -/
def headerFor (name : String) : IO (Array String) := do
  let some pair := headers.find? (·.1 == name) | throw <| IO.userError s!"unknown publication table {name}"
  return pair.2

/-- A publication input collection is independent of the phase checker and its strict lexical reader. -/
structure Data where
  root : FilePath
  tables : Std.HashMap String (Array Row)

/-- Fetch an explicitly loaded table; absent inputs cannot pass vacuously. -/
def Data.rows (data : Data) (name : String) : IO (Array Row) := do
  let some rows := data.tables[name]? | throw <| IO.userError s!"missing publication input {name}"
  return rows

/-- Load exactly the required publication tables, or an explicit derive-only subset. -/
def load (root : FilePath) (names : Array String := headers.map Prod.fst) : IO Data := do
  let mut tables := {}
  for name in names do
    tables := tables.insert name (← readTsv (root / "registry" / (name.replace "_" "-" ++ ".tsv")) (← headerFor name))
  return ⟨root,tables⟩

/-- Construct a string-valued row without leaking an input row's private columns. -/
def stringRow (fields : Array (String × String)) : Row := Json.mkObj (fields.toList.map fun (k,v) => (k,toJson v))

/-- Copy only an explicitly permitted set of public columns. -/
def project (row : Row) (names : Array String) : IO Json := do
  Json.mkObj <$> names.toList.mapM (fun name => do pure (name,← field row name))

/-- Parse the ordinary integer positions used by the publication sort, without imposing positivity. -/
def integer (text : String) : IO Int := Checker.Text.integer text

/-- Index stable identities uniquely, retaining the exact public duplicate diagnostic. -/
def indexUnique (rows : Array Row) (key description : String) : IO (Std.HashMap String Row) := do
  let mut result := {}
  for row in rows do
    let value ← str row key
    require (!result.contains value) s!"duplicate {description} {value}"
    result := result.insert value row
  return result

/-- Read a required stable identity rather than fabricating an empty record. -/
def lookup (rows : Std.HashMap String Row) (key : String) : IO Row := do
  let some row := rows[key]? | throw <| IO.userError s!"unknown publication identity {key}"
  return row

end Checker.Publication
