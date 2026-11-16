import Checker.Support

/-! Reviewed same-page locator maintenance, with immutable event-owned history. -/
namespace Checker.Locations
open Lean Checker.CheckAll

/-- Locator history consumes the same exact TSV fields as the registry validators. -/
abbrev Row := Array String

/-- Read a one-based field; schema owners reject malformed row lengths. -/
private def cell (row : Row) (position : Nat) : String := row[position - 1]?.getD ""

/-- Preserve the registry's stable-ID lookup without iterating unordered values for output. -/
private def indexed (rows : Array Row) : Std.HashMap String Row :=
  rows.foldl (fun result row => result.insert (cell row 1) row) {}

/-- Location identities use a reviewed ASCII token and at least four final decimal digits. -/
private def amendmentId (value : String) : Bool :=
  let parts := value.splitOn "-"
  let middle := String.intercalate "-" ((parts.drop 1).dropLast)
  let ending := parts.getLast!
  let alnum := fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
  let token := match middle.toList with
    | [] => false
    | first :: rest => alnum first && rest.all (fun c => alnum c || "._:#@+-".contains c)
  value.startsWith "LA-" && token && ending.length ≥ 4 &&
    ending.toList.all (fun c => '0' ≤ c && c ≤ '9')

/-- A location pair owns one existing singleton item relation in both revisions. -/
private def singleton (relations : Array Row) (claim item : String) : Bool :=
  let selected := relations.filter fun row => cell row 1 == item || cell row 3 == claim
  selected == #[#[item,"1",claim]]

/-- A refined locator preserves the exact printed-page, physical-page and section prefix. -/
private def samePagePrefix (old current : String) (page : Row) : Bool :=
  let before := (old.splitOn "; ").toArray
  let after := (current.splitOn "; ").toArray
  before.size ≥ 4 && after.size ≥ 4 && before.extract 0 3 == after.extract 0 3 &&
    before[0]?.getD "" == "PDF p. " ++ cell page 5 &&
    before[1]?.getD "" == "print p. " ++ cell page 4 &&
    (before[2]?.getD "").startsWith "§" && old != current

/-- Every owned amendment is unique, source ordered and linked into an exact old/new chain. -/
private structure HistoryState where
  ids : Std.HashSet String := {}
  owners : Std.HashSet String := {}
  eventClaims : Std.HashSet (String × String) := {}
  claimItems : Std.HashMap String String := {}
  itemClaims : Std.HashMap String String := {}
  tails : Std.HashMap (String × String) (String × String) := {}
  eventPosition : Nat := 0

/-- Validate the complete append-only history and its exact current claim/item endpoints. -/
def validateHistory (claims items pages relations events reviews corrections amendments : Array Row) : IO Unit := do
  let claimIndex := indexed claims; let itemIndex := indexed items; let pageIndex := indexed pages
  let eventIndex := indexed events; let reviewIndex := indexed reviews; let correctionIndex := indexed corrections
  let state ← amendments.foldlM (fun state row => do
    require (row.size == 10 && !state.ids.contains (cell row 1) && amendmentId (cell row 1))
      "invalid source-location amendment identity"
    let event := cell row 2; let owner := cell row 3; let claim := cell row 4; let item := cell row 5
    let action := correctionIndex[owner]?.getD #[]
    let readiness := reviewIndex[cell action 4]?.getD #[]
    let eventRow := eventIndex[event]?.getD #[]
    let some position := (cell eventRow 2).toNat? | throw <| IO.userError "source-location event is unknown"
    require (position > 0 && state.eventPosition ≤ position && !state.owners.contains owner &&
      !state.eventClaims.contains (event,claim) && cell action 2 == event && cell action 5 == claim &&
      cell action 6 == "amend_location" && cell action 7 == cell action 9 && cell action 8 == cell action 10 &&
      cell readiness 2 == event && cell readiness 4 == claim &&
      cell readiness 5 == "source_location_readiness" && cell readiness 6 == "amend_location" &&
      cell readiness 7 == "closed" && cell readiness 9 == cell row 10 && cell row 10 == cell eventRow 5)
      "source-location amendment lacks its unique closed event review"
    let claimRow := claimIndex[claim]?.getD #[]; let itemRow := itemIndex[item]?.getD #[]
    let page := pageIndex[cell claimRow 4]?.getD #[]
    require (!claimRow.isEmpty && !itemRow.isEmpty && !page.isEmpty &&
      cell claimRow 2 == cell eventRow 3 && cell itemRow 2 == cell claimRow 2 &&
      cell page 2 == cell claimRow 2 && cell itemRow 4 == cell claimRow 4 &&
      singleton relations claim item &&
      (state.claimItems[claim]?.isNone || state.claimItems[claim]? == some item) &&
      (state.itemClaims[item]?.isNone || state.itemClaims[item]? == some claim))
      "source-location amendment changes its source, page or singleton membership"
    require (samePagePrefix (cell row 6) (cell row 7) page &&
      samePagePrefix (cell row 8) (cell row 9) page &&
      ((cell row 6).splitOn "; ").take 3 == ((cell row 8).splitOn "; ").take 3)
      "source-location amendment changes its frozen page or section prefix"
    if let some previous := state.tails[(claim,item)]? then
      require (previous == (cell row 6,cell row 8)) "source-location amendment chain is broken"
    return { state with
      ids := state.ids.insert (cell row 1)
      owners := state.owners.insert owner
      eventClaims := state.eventClaims.insert (event,claim)
      claimItems := state.claimItems.insert claim item
      itemClaims := state.itemClaims.insert item claim
      tails := state.tails.insert (claim,item) (cell row 7,cell row 9)
      eventPosition := position })
    ({} : HistoryState)
  let locationActions := corrections.filter (cell · 6 == "amend_location")
  require (locationActions.size == state.owners.size && locationActions.all (fun row => state.owners.contains (cell row 1)))
    "source-location corrections and amendments are not bijective"
  for ((claim,item),tail) in state.tails do
    require (cell (claimIndex[claim]?.getD #[]) 5 == tail.1 &&
      cell (itemIndex[item]?.getD #[]) 8 == tail.2) "source-location current endpoint differs from its history"

/-- Only exact event-owned locator replacements can alter existing claim or item records. -/
def validateTransition (oldClaims oldItems oldRelations claims items relations oldAmendments amendments : Array Row)
    (event : String) : IO Unit := do
  let beforeClaims := indexed oldClaims; let beforeItems := indexed oldItems
  let afterClaims := indexed claims; let afterItems := indexed items
  let oldIds := indexed oldAmendments
  let fresh := amendments.filter fun row => !oldIds.contains (cell row 1)
  for row in fresh do
    let claim := cell row 4; let item := cell row 5
    let oldClaim := beforeClaims[claim]?.getD #[]; let oldItem := beforeItems[item]?.getD #[]
    require (cell row 2 == event && !oldClaim.isEmpty && !oldItem.isEmpty &&
      cell oldClaim 5 == cell row 6 && cell oldItem 8 == cell row 8 &&
      afterClaims[claim]? == some (oldClaim.set! 4 (cell row 7)) &&
      afterItems[item]? == some (oldItem.set! 7 (cell row 9)) &&
      singleton oldRelations claim item && singleton relations claim item)
      "source-location transition changes unowned fields or its recorded old values"
  for row in oldClaims do
    let current := afterClaims[cell row 1]?.getD #[]
    if cell current 5 != cell row 5 then
      require (fresh.any fun amendment => cell amendment 4 == cell row 1 &&
        cell amendment 6 == cell row 5 && cell amendment 7 == cell current 5)
        "claim locator changed without an owned source-location amendment"
  for row in oldItems do
    let current := afterItems[cell row 1]?.getD #[]
    if cell current 8 != cell row 8 then
      require (fresh.any fun amendment => cell amendment 5 == cell row 1 &&
        cell amendment 8 == cell row 8 && cell amendment 9 == cell current 8)
        "item locator changed without an owned source-location amendment"

end Checker.Locations
