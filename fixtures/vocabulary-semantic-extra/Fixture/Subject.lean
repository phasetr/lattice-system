module

public import Init

@[expose] public section

namespace Fixture

/-- A registered fixture declaration. -/
abbrev Item := Nat

/-- An intentionally unregistered fixture declaration. -/
abbrev Extra := Nat

end Fixture
