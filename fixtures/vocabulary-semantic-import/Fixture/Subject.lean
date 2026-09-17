module

public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Fixture

/-- A declaration whose module has an intentionally mismatched import registry. -/
abbrev Item := Nat

end Fixture
