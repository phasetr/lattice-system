import Checker.Support

/-! Shared Unicode text and integer input contracts; C-locale schema rules stay separate. -/
namespace Checker.Text
open Checker.CheckAll

/-- The Unicode whitespace accepted by the original text field contract. -/
def whitespace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || (28 ≤ n && n ≤ 32) ||
    #[0x85,0xa0,0x1680,0x2028,0x2029,0x202f,0x205f,0x3000].contains n ||
    (0x2000 ≤ n && n ≤ 0x200a)

/-- Trim the same Unicode whitespace at both ends without touching the normalized body itself. -/
def strip (text : String) : String :=
  String.ofList (((text.toList.dropWhile whitespace).reverse.dropWhile whitespace).reverse)

/-- Decimal digit blocks accepted by Unicode decimal integer parsing. -/
def decimal (c : Char) : Option Nat := do
  let n := c.toNat
  let starts := #[0x30,0x660,0x6f0,0x7c0,0x966,0x9e6,0xa66,0xae6,0xb66,0xbe6,0xc66,0xce6,
    0xd66,0xde6,0xe50,0xed0,0xf20,0x1040,0x1090,0x17e0,0x1810,0x1946,0x19d0,0x1a80,
    0x1a90,0x1b50,0x1bb0,0x1c40,0x1c50,0xa620,0xa8d0,0xa900,0xa9d0,0xa9f0,0xaa50,
    0xabf0,0xff10,0x104a0,0x10d30,0x11066,0x110f0,0x11136,0x111d0,0x112f0,0x11450,
    0x114d0,0x11650,0x116c0,0x11730,0x118e0,0x11950,0x11c50,0x11d50,0x11da0,0x16a60,
    0x16ac0,0x16b50,0x1d7ce,0x1d7d8,0x1d7e2,0x1d7ec,0x1d7f6,0x1e140,0x1e2f0,0x1e950,0x1fbf0]
  let first ← starts.find? (fun start => start ≤ n && n < start + 10)
  return n-first

/-- Parse signed event ordinals, including surrounding Unicode whitespace and digit separators. -/
def integer (value : String) : IO Int := do
  let chars := (strip value).toList
  let (negative, chars) := match chars with
    | '-' :: tail => (true,tail)
    | '+' :: tail => (false,tail)
    | _ => (false,chars)
  let mut result := 0
  let mut priorDigit := false
  let mut valid := !chars.isEmpty
  for c in chars do
    if c == '_' then
      valid := valid && priorDigit
      priorDigit := false
    else if let some digit := decimal c then
      result := result*10 + digit
      priorDigit := true
    else valid := false
  require (valid && priorDigit) ("invalid literal for int() with base 10: '" ++ value ++ "'")
  return if negative then -(Int.ofNat result) else Int.ofNat result


/-- Preserve the CLI's lone dash and negative decimal value handling. -/
def optionToken (value : String) : Bool :=
  if value == "-" || !value.startsWith "-" then false else
  let digits := fun text : String => text.toList.all (fun c => (decimal c).isSome)
  let parts := (value.drop 1).toString.splitOn "."
  let negativeNumber := match parts with
    | [whole] => !whole.isEmpty && digits whole
    | [whole,fraction] => digits whole && !fraction.isEmpty && digits fraction
    | _ => false
  !negativeNumber

end Checker.Text
