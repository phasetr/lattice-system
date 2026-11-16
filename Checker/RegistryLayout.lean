import Checker.Support

/-! Read-only normalization of physical registry layouts into the established logical tables. -/
namespace Checker.RegistryLayout
open Checker.CheckAll

/-- Exact observed bytes, keyed by their repository-relative registry path. -/
abbrev Files := Std.HashMap String String

/-- Current entry points require compact sources; explicit historical readers retain old layouts. -/
inductive Profile where
  | current
  | historical
  | legacyFixture
  deriving BEq, Repr

/-- A normalized view never rewrites the observed files on disk. -/
structure View where
  compact : Bool
  files : Files

/-- The original source identity columns retain their exact order and meaning. -/
def legacySourceHeader : String :=
  "source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage"

/-- Compact sources retain the sixteen identity columns and one authoritative lifecycle. -/
def sourceHeader : String :=
  String.intercalate "\t" (((split legacySourceHeader "\t").extract 0 16).toList) ++
    "\tlifecycle\tlifecycle_review_ref\tphysical_page_count\tcensus_oid\tcensus_review_ref"

/-- The logical lifecycle table is derived only from compact source suffixes. -/
def progressHeader : String := "source_id\tlifecycle\treview_ref"

/-- Logical counts are derived; the physical page count and census OID remain independent anchors. -/
def invariantHeader : String :=
  "source_id\tphysical_page_count\tactive_claim_count\tformalization_target_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref"

/-- Historical source items retain their original eleven-column schema and tag value. -/
def legacyItemHeader : String :=
  "item_id\tsource_id\torder_key\tpage_id\titem_kind\tsource_label\ttitle\tlocator\tpublic_group\tpublic_slug\treview_ref"

/-- Compact source items store their ten variable metadata columns only. -/
def currentItemHeader : String :=
  String.intercalate "\t" (((split legacyItemHeader "\t").extract 0 10).toList)

/-- The removed item column is a fixed format tag, not an independent mathematical review. -/
def fixedItemFormatTag : String := "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"

/-- These pre-R4 tables may be physically absent only in the compact layout. -/
def futureHeaders : Array (String × String) := #[
  ("slices", "slice_id\tposition\tclaim_id"),
  ("dependencies", "claim_id\trole\ttarget_claim_id\trationale"),
  ("bindings", "claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref"),
  ("claim-context", "claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref"),
  ("axioms", "axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid"),
  ("claim-axioms", "claim_id\taxiom_id"),
  ("statement-modules", "module\tsource_path\trole"),
  ("statement-imports", "module\tposition\timported_module\tis_exported\tis_meta\timport_all")]

private abbrev Row := Array String

private def path (stem : String) : String := "registry/" ++ stem ++ ".tsv"

/-- Split LF records without dropping internal blank rows or changing CR and field whitespace. -/
private def records (text : String) : Array String :=
  let result := split text "\n"
  if text.endsWith "\n" then result.pop else result

/-- Only normalization-owned schemas are interpreted here; all other raw bytes pass through. -/
private def table (text header stem : String) : IO (Array Row) := do
  let lines := records text
  require (text.contains '\n' && lines[0]? == some header) s!"bad {stem}.tsv header for registry layout"
  let width := (split header "\t").size
  let rows := (lines.extract 1 lines.size).map (split · "\t")
  require (rows.all (fun row => row.size == width)) s!"bad {stem}.tsv row width for registry layout"
  return rows

private def cell (row : Row) (position : Nat) : String := row[position - 1]?.getD ""

private def encode (header : String) (rows : Array Row) : String :=
  header ++ "\n" ++ String.join (rows.toList.map fun row => String.intercalate "\t" row.toList ++ "\n")

/-- Match the existing ASCII registry review grammar, including its permitted slash. -/
private def token (text : String) : Bool :=
  let alnum := fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
  match text.toList with
  | [] => false
  | first :: rest => alnum first && rest.all (fun c => alnum c || "._:/#@+-".contains c)

private def positiveDecimal (text : String) : Bool :=
  !text.isEmpty && !text.startsWith "0" && text.toList.all (fun c => '0' ≤ c && c ≤ '9')

private def oid (text : String) : Bool := hex text 40 || hex text 64

/-- Stage ranks are source-local; they do not derive or replace the global phase. -/
private def rank (lifecycle : String) : Nat :=
  ((#["registered", "source_frozen", "census_pass1", "census_pass2", "census_reconciled",
    "vocabulary_reviewed", "skeleton_frozen", "proof_active", "complete"].findIdx? (· == lifecycle)).map (· + 1)).getD 0

/-- Reconstruct only the coverage already required by the historical lifecycle validator. -/
private def lifecycleCoverage (lifecycle : String) : Option String :=
  match lifecycle with
  | "registered" | "source_frozen" => some "pending"
  | "census_pass1" => some "pass1"
  | "census_pass2" => some "pass2"
  | "census_reconciled" => some "reconciled"
  | "vocabulary_reviewed" | "skeleton_frozen" | "proof_active" | "complete" => some "frozen"
  | _ => none

/-- Compact anchors are absent together before reconciliation and present together afterwards. -/
private def validateSuffix (row : Row) : IO Unit := do
  let stage := rank (cell row 17)
  require (stage > 0) "bad source lifecycle"
  require (token (cell row 18)) "bad source progress review token"
  let anchor := #[cell row 19, cell row 20, cell row 21]
  let absent := anchor.all (· == "NONE")
  require (absent || (!anchor.any (· == "NONE") && positiveDecimal (cell row 19) &&
    oid (cell row 20) && token (cell row 21)))
    "invalid compact source census anchors"
  require ((stage ≥ 5) == !absent) "reconciled source invariant membership mismatch"

/-- Parsed callers retain their own TSV dialect; this projection never re-splits field values.
    Compact anchor rows contain source ID, physical page count, census OID and review reference.
    Historical projections deliberately have no synthesized progress or anchor tables. -/
structure SourceProjection where
  compact : Bool
  header : Array String
  rows : Array (Array String)
  progress : Option (Array (Array String))
  anchors : Option (Array (Array String))

/-- Validate the source schema and project parsed compact rows without changing identity fields. -/
def projectSources (header : Array String) (rows : Array (Array String))
    (profile : Profile) : IO SourceProjection := do
  if header == split legacySourceHeader "\t" then
    require (profile != .current) "current registry requires compact sources.tsv"
    require (rows.all (fun row => row.size == 17)) "bad sources.tsv row width for registry layout"
    return { compact := false, header := header, rows := rows, progress := none, anchors := none }
  require (header == split sourceHeader "\t") "bad sources.tsv header for registry layout"
  require (rows.all (fun row => row.size == 21)) "bad sources.tsv row width for registry layout"
  let logical ← rows.mapM fun row => do
    validateSuffix row
    let some coverage := lifecycleCoverage (cell row 17) | throw <| IO.userError "bad source lifecycle"
    return (row.extract 0 16).push coverage
  return {
    compact := true
    header := split legacySourceHeader "\t"
    rows := logical
    progress := some (rows.map fun row => #[cell row 1, cell row 17, cell row 18])
    anchors := some ((rows.filter (fun row => cell row 19 != "NONE")).map fun row =>
      #[cell row 1, cell row 19, cell row 20, cell row 21]) }

/-- Parsed source-item fields retain the caller's literal or quoted TSV interpretation. -/
structure ItemProjection where
  header : Array String
  rows : Array (Array String)

/-- Restore the fixed tag only for compact items; historical tag values remain unmodified. -/
def projectItems (header : Array String) (rows : Array (Array String))
    (compact : Bool) : IO ItemProjection := do
  let expected := if compact then currentItemHeader else legacyItemHeader
  let width := if compact then 10 else 11
  require (header == split expected "\t") "bad source-items.tsv header for registry layout"
  require (rows.all (fun row => row.size == width)) "bad source-items.tsv row width for registry layout"
  return {
    header := split legacyItemHeader "\t"
    rows := if compact then rows.map (·.push fixedItemFormatTag) else rows }

/-- Project one known future table; the stem is its bare table name, never a file path.
    Parsed rows keep the caller's TSV dialect and are never serialized or re-split here. -/
def projectFuture (phase stem : String)
    (observed : Option (Array String × Array (Array String))) : IO (Array (Array String)) := do
  require (#["bootstrap", "census", "vocabulary", "skeleton", "proof"].contains phase)
    "unknown phase for registry layout"
  let some (_, expected) := futureHeaders.find? (·.1 == stem) |
    throw <| IO.userError "unknown future table for registry layout"
  let preR4 := #["bootstrap", "census", "vocabulary"].contains phase
  let some (header, rows) := observed | do
    require preR4 s!"missing {stem}.tsv in post-R4 compact registry"
    return #[]
  let columns := split expected "\t"
  require (header == columns) s!"bad {stem}.tsv header for registry layout"
  require (rows.all (fun row => row.size == columns.size)) s!"bad {stem}.tsv row width for registry layout"
  require (!preR4 || rows.isEmpty) s!"pre-R4 compact registry requires header-only {stem}.tsv"
  return rows

/-- One source's census arithmetic retains excluded active claims in page usage and active counts. -/
private structure Counts where
  active : Nat := 0
  targets : Nat := 0
  equations : Nat := 0
  emptyPages : Nat := 0

/-- Derive the old four counters in linear corpus passes without replacing the independent anchors. -/
private def censusCounts (pages claims : Array Row) : Std.HashMap String Counts :=
  let (counts, usedPages) := claims.foldl (fun (counts, usedPages) row =>
    if cell row 12 != "false" then (counts, usedPages) else
      let source := cell row 2
      let current := counts[source]?.getD ({} : Counts)
      let updated := { current with
        active := current.active + 1
        targets := current.targets + (if cell row 6 != "out_of_scope" then 1 else 0)
        equations := current.equations + (if cell row 7 == "equation" then 1 else 0) }
      (counts.insert source updated, usedPages.insert (source, cell row 4)))
      (({} : Std.HashMap String Counts), ({} : Std.HashSet (String × String)))
  pages.foldl (fun counts row =>
    let source := cell row 2
    let current := counts[source]?.getD ({} : Counts)
    if usedPages.contains (source, cell row 1) then counts else
      counts.insert source { current with emptyPages := current.emptyPages + 1 }) counts

private def pageHeader : String :=
  "page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid"

private def claimHeader : String :=
  "claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref"

/-- Derive census views only when both corpus inputs were actually loaded by the caller. -/
private def invariantRows (raw : Files) (anchors : Array Row) : IO (Option (Array Row)) := do
  let some pages := raw[path "pages"]? | return none
  let some claims := raw[path "claims"]? | return none
  let counts := censusCounts (← table pages pageHeader "pages") (← table claims claimHeader "claims")
  return some (anchors.map fun row =>
    let source := cell row 1
    let count := counts[source]?.getD ({} : Counts)
    #[source, cell row 2, toString count.active, toString count.targets, toString count.equations,
      toString count.emptyPages, cell row 3, cell row 4])

/-- Native readers retain literal tab fields and exact header termination requirements. -/
private def parsed (text stem : String) : IO (Array String × Array Row) := do
  require (text.contains '\n') s!"bad {stem}.tsv header for registry layout"
  let lines := records text
  return (split (lines[0]?.getD "") "\t", (lines.extract 1 lines.size).map (split · "\t"))

/-- Only a loaded compact item table is projected; absence remains observable to its owner. -/
private def normalizeItems (raw files : Files) : IO Files := do
  let some text := raw[path "source-items"]? | return files
  let (header, rows) ← parsed text "source-items"
  let projection ← projectItems header rows true
  return files.insert (path "source-items") (encode legacyItemHeader projection.rows)

/-- A phase-aware caller decides whether absent future tables are legitimate pre-R4 structure. -/
private def normalizeFuture (raw files : Files) : IO Files := do
  let some phaseText := raw[path "phase"]? |
    throw <| IO.userError "compact registry requires phase.tsv"
  let phaseRows ← table phaseText "phase" "phase"
  require (phaseRows.size == 1) "invalid phase for registry layout"
  let phase := cell phaseRows[0]! 1
  require (#["bootstrap", "census", "vocabulary", "skeleton", "proof"].contains phase)
    "unknown phase for registry layout"
  futureHeaders.foldlM (fun files (stem, header) => do
    let observed ← match raw[path stem]? with
      | some text => some <$> parsed text stem
      | none => pure none
    discard <| projectFuture phase stem observed
    return if observed.isSome then files else files.insert (path stem) (header ++ "\n")) files

/-- Normalize only the explicit compact schema; historical layouts remain literal observations. -/
def normalize (raw : Files) (profile : Profile) : IO View := do
  let some sourceText := raw[path "sources"]? |
    if profile == .current then throw <| IO.userError "current registry requires compact sources.tsv"
    else return { compact := false, files := raw }
  let lines := records sourceText
  require (sourceText.contains '\n') "bad sources.tsv header for registry layout"
  let projection ← projectSources (split (lines[0]?.getD "") "\t")
    ((lines.extract 1 lines.size).map (split · "\t")) profile
  if !projection.compact then return { compact := false, files := raw }
  require (!raw.contains (path "source-progress") && !raw.contains (path "source-invariants"))
    "compact sources cannot coexist with legacy source state tables"
  let files := raw.insert (path "sources") (encode legacySourceHeader projection.rows)
    |>.insert (path "source-progress") (encode progressHeader (projection.progress.getD #[]))
  let files ← match ← invariantRows raw (projection.anchors.getD #[]) with
    | some rows => pure (files.insert (path "source-invariants") (encode invariantHeader rows))
    | none => pure files
  let files ← normalizeItems raw files
  return { compact := true, files := ← normalizeFuture raw files }

end Checker.RegistryLayout
