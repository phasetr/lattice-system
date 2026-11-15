import Checker.Publication.Tabular

/-! Locator-derived public items preserve source order and independently registered stable identities. -/
namespace Checker.Publication
open Lean System Checker.CheckAll

/-- Unicode whitespace used by the original text reader, independent of C-locale registry hygiene. -/
def textSpace (c : Char) : Bool := Checker.Text.whitespace c

/-- Strip only the original Unicode whitespace set. -/
def strip (text : String) : String := Checker.Text.strip text

/-- Stable ASCII digit grammar used by locator patterns, rather than numeric-value guessing. -/
def decimal (text : String) : Bool := !text.isEmpty && text.toList.all (fun c => '0' ≤ c && c ≤ '9')

/-- Only ASCII alphabetic section labels are recognized by the printed locator grammar. -/
def letters (text : String) : Bool := !text.isEmpty && text.toList.all fun c =>
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

/-- Capture a leading source label, preserving its exact comma and whitespace boundary. -/
def labelPart (segment : String) : Option (String × String) := Id.run do
  for (headingWord,kind) in #[
    ("Theorem","theorem"),("Lemma","lemma"),("Corollary","corollary"),("Proposition","proposition"),
    ("Definition","definition"),("Problem","problem"),("Conjecture","conjecture"),("Example","example"),("Exercise","exercise")] do
    if segment.startsWith headingWord then
      let suffix := (segment.drop headingWord.length).toString
      if suffix.toList.head?.any textSpace then
        let body := String.ofList (suffix.toList.dropWhile textSpace)
        let capture := (body.splitOn ",").head!
        if !capture.isEmpty then return some (kind,headingWord ++ " " ++ capture)
  for (headingWord,kind) in #[("Remark","remark"),("Note","note")] do
    let marker := headingWord ++ " unnumbered line "
    if segment.startsWith marker then
      let digits := String.ofList (((segment.drop marker.length).toString.toList).takeWhile (fun c => '0' ≤ c && c ≤ '9'))
      if !digits.isEmpty then return some (kind,marker ++ digits)
  for headingWord in #["equation","Equation"] do
    if segment.startsWith headingWord then
      let suffix := (segment.drop headingWord.length).toString
      if suffix.toList.head?.any textSpace then
        let body := String.ofList (suffix.toList.dropWhile textSpace)
        if body.startsWith "(" then
          let beforeSemicolon := (((body.drop 1).toString.splitOn ";").head!).toList.toArray
          let mut ending := none
          for i in [:beforeSemicolon.size] do
            if beforeSemicolon[i]! == ')' then ending := some i
          if let some i := ending then
            if i > 0 then
              let middle := String.ofList (beforeSemicolon.extract 0 i).toList
              return some ("equation",headingWord ++ (String.ofList (suffix.toList.takeWhile textSpace)) ++ "(" ++ middle ++ ")")
  for (headingWord,kind) in #[("Fig.","figure"),("Footnote","footnote"),("Table","table")] do
    if segment.startsWith headingWord then
      let suffix := (segment.drop headingWord.length).toString
      if suffix.toList.head?.any textSpace then
        let whitespace := String.ofList (suffix.toList.takeWhile textSpace)
        let body := String.ofList ((suffix.drop whitespace.length).toString.toList.takeWhile fun c => c != ' ' && c != ',' && c != ';')
        if !body.isEmpty then return some (kind,headingWord ++ whitespace ++ body)
  return none

/-- Locate labels only within semicolon-delimited locator segments. -/
def extractLabel (locator : String) : String × String × String := Id.run do
  let segments := (split locator ";").map strip
  for i in [:segments.size] do
    if let some (kind,label) := labelPart segments[i]! then
      return (kind,label,String.intercalate "; " ((segments.extract 0 i).toList ++ [label]))
  return ("unlabeled","NONE",locator)

/-- Normalize a public group slug without changing named section semantics. -/
def slugForGroup (group : String) : IO String := do
  let text := strip group
  if (text.toLower).startsWith "chapter" then
    let suffix := (text.drop 7).toString
    let number := String.ofList (suffix.toList.dropWhile textSpace)
    if suffix.toList.head?.any textSpace && decimal number then
      let n ← integer number
      let value := toString n
      return "chapter-" ++ String.ofList (List.replicate (2-value.length) '0') ++ value
  let lowered := String.join (group.toList.map fun c =>
    if c == 'İ' then "i\u0307" else if c == 'K' then "k" else (String.singleton c).toLower)
  let mut slug := ""; let mut separator := false
  for c in lowered.toList do
    if ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') then
      if separator && !slug.isEmpty then slug := slug.push '-'
      slug := slug.push c; separator := false
    else separator := true
  require (!slug.isEmpty) s!"public group has no safe slug: {group}"
  return slug

/-- Recognize a top-level printed section, with the original suffix boundary. -/
def sectionTop (text : String) (locator : Bool) : Option String := do
  if !text.startsWith "§" then none else do
    let suffix := (text.drop 1).toString
    let digits := String.ofList (suffix.toList.takeWhile (fun c => '0' ≤ c && c ≤ '9'))
    let top := if !digits.isEmpty then digits else String.ofList (suffix.toList.takeWhile fun c =>
      ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z'))
    if top.isEmpty then none else
      let remaining := (suffix.drop top.length).toString
      if remaining.isEmpty || remaining.startsWith "." || (locator && remaining.startsWith ";") then some top else none

/-- Derive display grouping from section metadata before the locator fallback. -/
def publicGroup (page : Row) (locator : String) : IO String := do
  let sectionText ← str page "section"
  let mut top := sectionTop sectionText false
  if top.isNone then
    for segment in locator.splitOn "; " do
      if let some value := sectionTop segment true then top := some value; break
  if let some value := top then
    if decimal value then
      let number := toString (← integer value)
      return "Chapter " ++ String.ofList (List.replicate (2-number.length) '0') ++ number
    else return "Appendix " ++ value.toUpper
  if #["Contents","Preface","Symbols"].contains sectionText then return "Front matter"
  if #["Index","References","Solutions"].contains sectionText then return sectionText
  return match ← str page "page_kind" with
    | "front_matter" => "Front matter"
    | "back_matter" => "Back matter"
    | "index" => "Index"
    | _ => "Ungrouped"

/-- Remove only a terminal reviewed successor ordinal, leaving every other locator byte intact. -/
def groupingLocator (locator : String) : String :=
  let marker := "; corpus correction successor "
  let parts := locator.splitOn marker
  match parts.reverse with
  | tail :: rest =>
    let numbers := tail.splitOn "/"
    if !rest.isEmpty && numbers.length == 2 && numbers.all decimal then String.intercalate marker rest.reverse else locator
  | _ => locator

/-- Derive reviewed seed metadata and ordered claim membership without allocating canonical registry identities. -/
def derive (claims pages sources tracks : Array Row) : IO (Array Row × Array Row) := do
  let pageById ← indexUnique pages "page_id" "page ID"
  let mut trackPositions : Std.HashMap String Int := {}
  for row in tracks do trackPositions := trackPositions.insert (← str row "track_id") (← integer (← str row "position"))
  let mut sourceOrder : Std.HashMap String (Int × Int) := {}
  for row in sources do
    let source ← str row "source_id"; let track ← str row "track_id"
    let some position := trackPositions[track]? | throw <| IO.userError s!"source refers to unknown track {source}"
    sourceOrder := sourceOrder.insert source (position,← integer (← str row "source_position"))
  let mut ordered := #[]
  for claim in claims do
    let id ← str claim "claim_id"; let source ← str claim "source_id"
    let some order := sourceOrder[source]? | throw <| IO.userError s!"claim refers to unknown source {id}"
    ordered := ordered.push ((order.1,order.2,← str claim "order_key",id),ordered.size,claim)
  ordered := ordered.qsort fun a b =>
    if a.1.1 != b.1.1 then a.1.1 < b.1.1 else
    if a.1.2.1 != b.1.2.1 then a.1.2.1 < b.1.2.1 else
    if a.1.2.2.1 != b.1.2.2.1 then a.1.2.2.1 < b.1.2.2.1 else
    if a.1.2.2.2 != b.1.2.2.2 then a.1.2.2.2 < b.1.2.2.2 else a.2.1 < b.2.1
  let mut groups : Array (String × Row × Array String) := #[]
  let mut positions : Std.HashMap String Nat := {}
  for (_,_,claim) in ordered do
    let id ← str claim "claim_id"; let source ← str claim "source_id"; let pageId ← str claim "page_id"
    let some page := pageById[pageId]? | throw <| IO.userError s!"claim refers to unknown page {id}"
    let locator := groupingLocator (← str claim "locator")
    let (kind,label,canonical) := extractLabel locator
    let key := (toJson #[source,pageId,if label == "NONE" then "locator" else "label",if label == "NONE" then locator else label]).compress
    if let some i := positions[key]? then
      let (oldKey,item,members) := groups[i]!
      require ((← str item "item_kind") == kind && (← str item "locator") == canonical) s!"inconsistent explicit source label {label}"
      groups := groups.set! i (oldKey,item,members.push id)
    else
      let group ← publicGroup page (← str claim "locator")
      let item := stringRow #[("source_id",source),("order_key",← str claim "order_key"),("page_id",pageId),
        ("item_kind",kind),("source_label",label),("title","NONE"),("locator",canonical),
        ("public_group",group),("public_slug",← slugForGroup group),("review_ref","PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1")]
      positions := positions.insert key groups.size
      groups := groups.push (key,item,#[id])
  let mut counts : Std.HashMap String Nat := {}; let mut items := #[]; let mut relations := #[]
  for (_,item,members) in groups do
    let source ← str item "source_id"; let n := counts[source]?.getD 0 + 1
    counts := counts.insert source n
    let number := toString n
    let id := "IT-" ++ source ++ "-" ++ String.ofList (List.replicate (4-number.length) '0') ++ number
    items := items.push (item.setObjVal! "item_id" (toJson id))
    for i in [:members.size] do relations := relations.push (stringRow #[("item_id",id),("position",toString (i+1)),("claim_id",members[i]!)])
  return (items,relations)

/-- Compare metadata independently of actual stable IDs, then preserve the raw relation order and total coverage. -/
def validateItems (data : Data) : IO Unit := do
  let claims ← data.rows "claims"
  let (expected,expectedRelations) ← derive claims (← data.rows "pages") (← data.rows "sources") (← data.rows "tracks")
  let actual ← data.rows "source_items"
  let columns := (← headerFor "source_items").filter (· != "item_id")
  let expectedMetadata ← expected.mapM (project · columns)
  let actualMetadata ← actual.mapM (project · columns)
  require (actualMetadata == expectedMetadata) "source-items.tsv metadata/order differs from locator-derived inventory"
  let members := fun (relations : Array Row) => do
    let mut grouped : Std.HashMap String (Array String) := {}
    for row in relations do
      let id ← str row "item_id"
      grouped := grouped.insert id ((grouped[id]?.getD #[]).push (← str row "claim_id"))
    return grouped
  let actualRelations ← data.rows "item_claims"
  let expectedClaims ← members expectedRelations; let actualClaims ← members actualRelations
  let expectedGroups ← expected.mapM fun row => do pure (expectedClaims[(← str row "item_id")]?.getD #[])
  let actualGroups ← actual.mapM fun row => do pure (actualClaims[(← str row "item_id")]?.getD #[])
  require (actualGroups == expectedGroups) "item-claims.tsv differs from locator-derived claim grouping"
  let registered ← claims.mapM (fun row => str row "claim_id")
  let mapped ← actualRelations.mapM (fun row => str row "claim_id")
  let set := fun values : Array String => values.foldl (fun (s : Std.HashSet String) id => s.insert id) {}
  let mappedSet := set mapped; let registeredSet := set registered
  require (mapped.size == mappedSet.size && mappedSet.size == registeredSet.size && registered.all mappedSet.contains)
    "registered claims are not covered exactly once"

end Checker.Publication
