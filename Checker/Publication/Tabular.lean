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

/-- The quoted reader carries one immutable record, field and lexical state through its scan. -/
private structure CsvState where
  result : Array (Array String) := #[]
  row : Array String := #[]
  value : String := ""
  quoted : Bool := false
  atStart : Bool := true
  touched : Bool := false

/-- Scan each character once, preserving doubled quotes, CRLF and non-strict unfinished quotes. -/
private partial def scanCsv (chars : Array Char) (i : Nat) (state : CsvState) : Array (Array String) :=
  if i >= chars.size then
    if state.touched || !state.row.isEmpty || !state.value.isEmpty then state.result.push (state.row.push state.value)
    else state.result
  else
    let c := chars[i]!
    if state.quoted then
      if c == '"' then
        if chars[i+1]? == some '"' then scanCsv chars (i+2) {state with value := state.value.push '"'}
        else scanCsv chars (i+1) {state with quoted := false}
      else scanCsv chars (i+1) {state with value := state.value.push c}
    else if c == '"' && state.atStart then
      scanCsv chars (i+1) {state with quoted := true, touched := true, atStart := false}
    else if c == '\t' then
      scanCsv chars (i+1) {state with row := state.row.push state.value, value := "", atStart := true, touched := true}
    else if c == '\n' || c == '\r' then
      let row := if state.touched || !state.row.isEmpty || !state.value.isEmpty then state.row.push state.value else #[]
      scanCsv chars (i + if c == '\r' && chars[i+1]? == some '\n' then 2 else 1)
        {result := state.result.push row}
    else scanCsv chars (i+1) {state with value := state.value.push c, touched := true, atStart := false}

/-- Decode standard non-strict quoted TSV, including quoted tabs/newlines and missing fields. -/
def csvRows (text : String) : Array (Array String) := scanCsv text.toList.toArray 0 {}

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
  let records ← rows.foldlM (fun records row => do
    let values ← header.mapM fun key => do
      let value ← field row key
      if value.isNull then pure "" else IO.ofExcept value.getStr?
    pure (records.push values)) #[header]
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
  let tables ← names.foldlM (fun tables name => do
    pure (tables.insert name (← readTsv (root / "registry" / (name.replace "_" "-" ++ ".tsv")) (← headerFor name))))
    ({} : Std.HashMap String (Array Row))
  return ⟨root,tables⟩

/-- Construct a string-valued row without leaking an input row's private columns. -/
def stringRow (fields : Array (String × String)) : Row := Json.mkObj (fields.toList.map fun (k,v) => (k,toJson v))

/-- Copy only an explicitly permitted set of public columns. -/
def project (row : Row) (names : Array String) : IO Json := do
  Json.mkObj <$> names.toList.mapM (fun name => do pure (name,← field row name))

/-- Parse the ordinary integer positions used by the publication sort, without imposing positivity. -/
def integer (text : String) : IO Int := Checker.Text.integer text

/-- Index stable identities uniquely, retaining the exact public duplicate diagnostic. -/
def indexUnique (rows : Array Row) (key description : String) : IO (Std.HashMap String Row) :=
  rows.foldlM (fun result row => do
    let value ← str row key
    require (!result.contains value) s!"duplicate {description} {value}"
    pure (result.insert value row)) {}

/-- Read a required stable identity rather than fabricating an empty record. -/
def lookup (rows : Std.HashMap String Row) (key : String) : IO Row := do
  let some row := rows[key]? | throw <| IO.userError s!"unknown publication identity {key}"
  return row

end Checker.Publication
