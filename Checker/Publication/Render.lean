import Checker.Publication.Catalog

/-! Deterministic public Markdown and JSON rendering, with a closed managed output tree. -/
namespace Checker.Publication
open Lean System Checker.CheckAll

/-- Byte-exact public rootTemplate format. -/
def rootTemplate : String := "# Formalization status\n\nThis public documentation is generated deterministically from the registered\nsource-item and claim metadata. It does not reproduce source claim text or\npublish private source paths and object identifiers.\n\n- Current phase: `{phase}`\n- Active atomic claims: {active_claims}\n- Formalization targets: {formalization_target_claims}\n- Superseded claim records: {tombstoned_claims}\n- Reviewed source items: {source_items}\n- Mathlib-only claims: {mathlib_only_claims}\n- Project-vocabulary claims: {project_vocabulary_claims}\n\nSee the [generated catalog](generated/index.md). Status values are deliberately\nconservative: `not_bound`, `not_recorded`, and `not_assessed` do not mean\nproved or axiom-free.\n"

/-- Byte-exact public indexTemplate format. -/
def indexTemplate : String := "# Generated registry catalog\n\nGenerated from the checked registries; do not edit by hand.\n\n## Summary\n\n- Phase: `{phase}`\n- Source items: {source_items}\n- Active claims: {active_claims}\n- Formalization targets: {formalization_target_claims}\n- Superseded claim records: {tombstoned_claims}\n- Vocabulary declarations: {vocabulary_declarations}\n- Claim-vocabulary links: {claim_vocabulary_links}\n\n## Tracks\n\n{tracks}\n\n## Sources\n\n{sources}\n\n## Public groups\n\n{groups}\n\nMachine-readable data: [catalog.json](catalog.json).\n"

/-- Byte-exact public trackTemplate format. -/
def trackTemplate : String := "# Track: {title}\n\n- Phase: `{phase}`\n- Active claims: {active_claims}\n- Formalization targets: {formalization_target_claims}\n- Superseded claim records: {tombstoned_claims}\n- Mathlib-only: {mathlib_only_claims}\n- Project vocabulary: {project_vocabulary_claims}\n- Complete claim-vocabulary links: {claim_vocabulary_links}\n\n## Sources\n\n{sources}\n\n## Registered vocabulary\n\n{vocabulary}\n\n`vocabulary_ready` records only vocabulary readiness to state future claims. It is not\na statement binding or proof status.\n"

/-- Byte-exact public sourceTemplate format. -/
def sourceTemplate : String := "# {title}\n\n- Source ID: `{source_id}`\n- Authors: {authors}\n- Year: `{year}`\n- Edition: `{edition}`\n- Identifier: `{identifier_kind}:{identifier}`\n- Public reference: {public_reference}\n- Registry lifecycle: `{coverage}`\n- Formalization lifecycle: `{lifecycle}`\n- Reviewed source items: {count}\n\nPrivate source paths and object identifiers are intentionally omitted.\n\n## Groups\n\n{groups}\n"

/-- Byte-exact public itemTemplate format. -/
def itemTemplate : String := "<a id=\"{item_id}\"></a>\n\n## {heading}\n\n- Item ID: `{item_id}`\n- Source: `{source_id}`\n- Page ID: `{page_id}`\n- Kind: `{item_kind}`\n- Source label: `{source_label}`\n{title_line}- Locator: {locator}\n\n### Atomic claims\n\n{claims}\n"

/-- Public HTML escaping preserves quotes, replaces line endings, and escapes Markdown table pipes. -/
def markdown (value : String) : String :=
  (((((value.replace "\r" " ").replace "\n" " ").replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "|" "&#124;"

/-- A formatting scalar preserves original human-readable null and Boolean spellings. -/
def scalar (value : Json) : String := match value with
  | .str text => text
  | .null => "None"
  | .bool true => "True"
  | .bool false => "False"
  | _ => value.compress

/-- Format a template in a single pass, never reinterpreting braces inside inserted public text. -/
def format (template : String) (values : Json) : IO String := do
  let chars := template.toList.toArray
  let mut i := 0; let mut output := ""
  while i < chars.size do
    if chars[i]! == '{' then
      if chars[i+1]? == some '{' then output := output.push '{'; i := i+2
      else
        let mut key := ""; i := i+1
        while i < chars.size && chars[i]! != '}' do key := key.push chars[i]!; i := i+1
        require (i < chars.size) "incomplete publication template"
        output := output ++ scalar (← field values key); i := i+1
    else if chars[i]! == '}' && chars[i+1]? == some '}' then output := output.push '}'; i := i+2
    else output := output.push chars[i]!; i := i+1
  return output

/-- Render sorted JSON keys, two-space indentation, raw Unicode and canonical empty collections. -/
partial def prettyJson (value : Json) (depth : Nat := 0) : String :=
  let indent := fun n => String.ofList (List.replicate n ' ')
  match value with
  | .arr rows => if rows.isEmpty then "[]" else
    "[\n" ++ String.intercalate ",\n" (rows.toList.map fun row => indent (depth+2) ++ prettyJson row (depth+2)) ++ "\n" ++ indent depth ++ "]"
  | .obj fields =>
    let entries := fields.foldl (fun result key row => result.push (key,row)) (#[] : Array (String × Json))
    if entries.isEmpty then "{}" else
      "{\n" ++ String.intercalate ",\n" (entries.toList.map fun (key,row) =>
        indent (depth+2) ++ (toJson key).compress ++ ": " ++ prettyJson row (depth+2)) ++ "\n" ++ indent depth ++ "}"
  | _ => value.compress

/-- One atomic claim's public status line does not reproduce its normalized source text. -/
def claimLine (claim : Json) : IO String := do
  let required ← arr claim "required_vocabulary"
  let names ← required.mapM fun row => do pure ("`" ++ (← str row "declaration") ++ "`")
  let requiredText := if names.isEmpty then "none" else String.intercalate ", " names.toList
  let successor ← str claim "successor_claim"
  return "- `" ++ (← str claim "claim_id") ++ "` — " ++ markdown (← str claim "disposition") ++ " / " ++ markdown (← str claim "subkind") ++
    "; lifecycle `" ++ (← str claim "lifecycle") ++ "`" ++
    (if successor != "NONE" then "; successor `" ++ successor ++ "`" else "") ++ "; " ++
    "Vocabulary `" ++ (← str claim "vocabulary_status") ++ "`; binding `" ++ (← str claim "binding_status") ++ "`; Lean statement `" ++
    scalar (← field claim "statement_declaration") ++ "` in `" ++ scalar (← field claim "statement_module") ++ "`; proof `" ++
    (← str claim "proof_status") ++ "` as `" ++ scalar (← field claim "proof_declaration") ++ "`; axioms `" ++
    (← str claim "axiom_status") ++ "`; required vocabulary: " ++ requiredText

/-- Gather JSON records satisfying an ordered predicate. -/
def select (values : Array Json) (predicate : Json → IO Bool) : IO (Array Json) := do
  let mut result := #[]
  for value in values do if ← predicate value then result := result.push value
  return result

/-- Build all and only the established public output families from the public projection. -/
def buildOutputs (catalog : Json) : IO (Std.HashMap String String) := do
  let summary ← field catalog "summary"; let phase ← field catalog "phase"
  let common := summary.setObjVal! "phase" phase
  let mut outputs := ({} : Std.HashMap String String)
  outputs := outputs.insert "docs/index.md" (← format rootTemplate common)
  let groups ← arr catalog "groups"; let sources ← arr catalog "sources"; let tracks ← arr catalog "tracks"
  let items ← arr catalog "items"; let vocabulary ← arr catalog "vocabulary"
  -- Reverse list buckets avoid both repeated full-item scans and copying a growing array on each insertion.
  let mut itemsBySource : Std.HashMap String (List Json) := {}
  let mut itemsByGroup : Std.HashMap (String × String) (List Json) := {}
  for item in items do
    let source ← str item "source_id"; let slug ← str item "public_slug"
    itemsBySource := itemsBySource.insert source (item :: (itemsBySource[source]?.getD []))
    let key := (source,slug)
    itemsByGroup := itemsByGroup.insert key (item :: (itemsByGroup[key]?.getD []))
  let mut groupLinks := #[]; let mut sourceLinks := #[]; let mut trackLinks := #[]
  for group in groups do groupLinks := groupLinks.push ("- [" ++ (← str group "source_id") ++ " / " ++ markdown (← str group "public_group") ++
    "](groups/" ++ (← str group "source_public_slug") ++ "/" ++ (← str group "public_slug") ++ ".md) — " ++ toString (← arr group "item_ids").size ++ " items")
  for source in sources do sourceLinks := sourceLinks.push ("- [" ++ (← str source "source_id") ++ "](sources/" ++ (← str source "public_slug") ++ ".md)")
  for track in tracks do trackLinks := trackLinks.push ("- [" ++ markdown (← str track "title") ++ "](tracks/" ++ (← str track "public_slug") ++ ".md)")
  let indexValues := common.mergeObj (Json.mkObj [("tracks",toJson (String.intercalate "\n" trackLinks.toList)),
    ("sources",toJson (String.intercalate "\n" sourceLinks.toList)),("groups",toJson (String.intercalate "\n" groupLinks.toList))])
  outputs := outputs.insert "docs/generated/index.md" (← format indexTemplate indexValues)
  for track in tracks do
    let trackId ← str track "track_id"
    let sourceRows ← select sources (fun source => do pure ((← str source "track_id") == trackId))
    let ids ← sourceRows.mapM (fun row => str row "source_id")
    let trackItems ← select items (fun item => do pure (ids.contains (← str item "source_id")))
    let mut trackClaims := #[]
    for item in trackItems do trackClaims := trackClaims ++ (← arr item "claims")
    let active ← select trackClaims (fun claim => do pure ((← str claim "lifecycle") == "active"))
    let targets ← select active (fun claim => do pure ((← str claim "disposition") != "out_of_scope"))
    let mut vocabularyIds : Std.HashSet String := {}; let mut linkCount := 0
    for claim in trackClaims do
      for row in ← arr claim "required_vocabulary" do
        vocabularyIds := vocabularyIds.insert (← str row "vocabulary_id"); linkCount := linkCount+1
    let mut sourceLines := #[]; let mut vocabularyLines := #[]
    for source in sourceRows do sourceLines := sourceLines.push ("- [`" ++ (← str source "source_id") ++ "`](../sources/" ++
      (← str source "public_slug") ++ ".md) — " ++ markdown (← str source "title") ++ "; lifecycle `" ++ (← str source "lifecycle") ++ "`")
    for row in vocabulary do
      if vocabularyIds.contains (← str row "vocabulary_id") then vocabularyLines := vocabularyLines.push (
        "- `" ++ (← str row "vocabulary_id") ++ "` — `" ++ (← str row "declaration") ++ "`; kind `" ++
        scalar (← field row "declaration_kind") ++ "`; role `" ++ scalar (← field row "design_role") ++ "`; finiteness `" ++ scalar (← field row "finiteness_scope") ++ "`")
    let mathlib ← countRows active (fun claim => do pure ((← str claim "vocabulary_basis") == "mathlib_only"))
    let projectCount ← countRows active (fun claim => do pure ((← str claim "vocabulary_basis") == "project_vocabulary"))
    let values := Json.mkObj [("title",toJson (markdown (← str track "title"))),("phase",phase),
      ("active_claims",toJson active.size),("formalization_target_claims",toJson targets.size),
      ("tombstoned_claims",toJson (trackClaims.size-active.size)),("mathlib_only_claims",toJson mathlib),
      ("project_vocabulary_claims",toJson projectCount),("claim_vocabulary_links",toJson linkCount),
      ("sources",toJson (String.intercalate "\n" sourceLines.toList)),
      ("vocabulary",toJson (if vocabularyLines.isEmpty then "- none" else String.intercalate "\n" vocabularyLines.toList))]
    outputs := outputs.insert ("docs/generated/tracks/" ++ (← str track "public_slug") ++ ".md") (← format trackTemplate values)
  for source in sources do
    let sourceId ← str source "source_id"; let sourceSlug ← str source "public_slug"
    let sourceItems := (itemsBySource[sourceId]?.getD []).reverse.toArray
    let publicUrl ← str source "public_url"
    let reference := if publicUrl == "NONE" then "`NONE`" else "[" ++ markdown publicUrl ++ "](" ++ markdown publicUrl ++ ")"
    let mut slugs := #[]; let mut titles : Std.HashMap String String := {}
    for item in sourceItems do
      let slug ← str item "public_slug"
      if !titles.contains slug then slugs := slugs.push slug
      titles := titles.insert slug (← str item "public_group")
    let mut links := #[]
    for slug in slugs do
      let members := itemsByGroup[(sourceId,slug)]?.getD []
      links := links.push ("- [" ++ markdown (titles[slug]?.getD "") ++ "](../groups/" ++ sourceSlug ++ "/" ++ slug ++ ".md) — " ++ toString members.length ++ " items")
    let mut values := source
    for key in #["title","authors","year","edition","identifier_kind","identifier","coverage","lifecycle"] do
      values := values.setObjVal! key (toJson (markdown (← str source key)))
    values := values.mergeObj (Json.mkObj [("public_reference",toJson reference),("count",toJson sourceItems.size),
      ("groups",toJson (String.intercalate "\n" links.toList))])
    outputs := outputs.insert ("docs/generated/sources/" ++ sourceSlug ++ ".md") (← format sourceTemplate values)
  for group in groups do
    let source ← str group "source_id"; let slug ← str group "public_slug"
    let groupItems := (itemsByGroup[(source,slug)]?.getD []).reverse.toArray
    let mut blocks := #[]
    for item in groupItems do
      let label ← str item "source_label"; let itemId ← str item "item_id"; let title ← str item "title"
      let heading := if label == "NONE" then "Unlabeled item " ++ itemId else label
      let titleLine := if title == "NONE" then "- Title: `NONE`\n" else "- Title: " ++ markdown title ++ "\n"
      let lines ← (← arr item "claims").mapM claimLine
      let values := item.mergeObj (Json.mkObj [("heading",toJson (markdown heading)),("title_line",toJson titleLine),
        ("locator",toJson (markdown (← str item "locator"))),("claims",toJson (String.intercalate "\n" lines.toList))])
      blocks := blocks.push (← format itemTemplate values)
    let text := "# Group " ++ source ++ " / " ++ markdown (← str group "public_group") ++ "\n\n" ++
      "Generated from reviewed source-item metadata. Source claim text is not reproduced.\n\n" ++ String.intercalate "\n" blocks.toList
    outputs := outputs.insert ("docs/generated/groups/" ++ (← str group "source_public_slug") ++ "/" ++ slug ++ ".md") text
  return outputs.insert "docs/generated/catalog.json" (prettyJson catalog ++ "\n")

/-- Walk only the managed generated tree; directory symlinks are never traversed. -/
partial def managedBelow (root current : FilePath) : IO (Array String × Array FilePath) := do
  let mut files := #[]; let mut directories := #[]
  for entry in ← current.readDir do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type == .dir then
      let (children,descendants) ← managedBelow root entry.path
      files := files ++ children; directories := directories ++ descendants ++ #[entry.path]
    else
      let regular ← if metadata.type == .file then pure true else if metadata.type == .symlink then do
        try pure ((← entry.path.metadata).type == .file) catch _ => pure false
        else pure false
      if regular then
        let parent := root.toString ++ "/"
        require (entry.path.toString.startsWith parent) "managed output escaped root"
        files := files.push (entry.path.toString.drop parent.length).toString
  return (files,directories)

/-- Enumerate the exact output ownership boundary, retaining stale files for comparison and safe retirement. -/
def outputMetadata (path : FilePath) : IO (Option IO.FS.Metadata) := do
  try return some (← path.symlinkMetadata)
  catch error => match error with
    | .noFileOrDirectory .. => return none
    | _ => throw error

/-- Validate every existing ancestor before creating a directory or walking managed files. -/
def outputDirectory (root : FilePath) (parts : List String) (create : Bool) : IO Bool := do
  let canonical ← IO.FS.realPath root
  require ((← root.symlinkMetadata).type == .dir) "output root is not a regular directory"
  let mut current := canonical
  for part in parts do
    require (!part.isEmpty && part != "." && part != "..") "unsafe generated output directory"
    current := current / part
    match ← outputMetadata current with
    | some metadata =>
      require (metadata.type == .dir && (← IO.FS.realPath current) == current)
        "generated output ancestor is not an owned directory"
    | none =>
      if !create then return false
      IO.FS.createDir current
  return true

/-- Enumerate only validated managed ancestors; symbolic parents never authorize an external walk. -/
def managedPaths (root : FilePath) : IO (Array String) := do
  let mut files := #[]
  unless ← outputDirectory root ["docs"] false do return files
  let index := root / "docs/index.md"
  if let some metadata ← outputMetadata index then
    require (metadata.type == .file) "expected generated output is not a regular file"
    files := files.push "docs/index.md"
  let generated := root / "docs/generated"
  if ← outputDirectory root ["docs","generated"] false then
    files := files ++ (← managedBelow root generated).1
  return files.qsort (· < ·)

/-- Output paths are a closed public family and may not escape to private or unrelated assets. -/
def outputPath (root : FilePath) (relative : String) : IO FilePath := do
  require (!relative.startsWith "/" && !(relative.splitOn "/").contains ".." &&
    (relative == "docs/index.md" || relative.startsWith "docs/generated/")) "unsafe generated output path"
  let path := root / relative
  discard <| outputDirectory root (relative.splitOn "/").dropLast true
  return path

/-- Regenerate expected bytes and retire only stale managed files, then collect empty generated directories. -/
def writeOutputs (root : FilePath) (outputs : Std.HashMap String String) : IO Unit := do
  for stale in ← managedPaths root do
    unless outputs.contains stale do IO.FS.removeFile (root / stale)
  let ordered := (outputs.toArray.map Prod.fst).qsort (· < ·)
  for relative in ordered do
    let path ← outputPath root relative
    let text := outputs[relative]?.getD ""
    if let some metadata ← outputMetadata path then
      require (metadata.type == .file) "expected generated output is not a regular file"
      if (← IO.FS.readFile path) != text then IO.FS.writeFile path text
    else IO.FS.writeFile path text
  let generated := root / "docs/generated"
  if ← generated.isDir then
    let (_,directories) ← managedBelow root generated
    for directory in directories.qsort (fun a b => a.components.length > b.components.length) do
      try IO.FS.removeDir directory catch _ => pure ()

/-- Missing, stale and outdated outputs are three distinct refusal classes, accumulated in stable order. -/
def checkOutputs (root : FilePath) (outputs : Std.HashMap String String) (quiet : Bool := false) : IO Bool := do
  let actual ← managedPaths root
  let expected := (outputs.toArray.map Prod.fst).qsort (· < ·)
  let mut errors := #[]
  for relative in expected do
    unless actual.contains relative do errors := errors.push ("missing generated file: " ++ relative)
  for relative in actual do
    unless outputs.contains relative do errors := errors.push ("stale generated file: " ++ relative)
  for relative in expected do
    if actual.contains relative && (← IO.FS.readFile (root / relative)) != outputs[relative]?.getD "" then
      errors := errors.push ("outdated generated file: " ++ relative)
  unless quiet do
    for error in errors do IO.eprintln ("generate-public-docs: " ++ error)
  return errors.isEmpty

end Checker.Publication
