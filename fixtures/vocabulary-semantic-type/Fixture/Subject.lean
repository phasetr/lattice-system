module

public import Init

@[expose] public section

namespace Fixture

/-- A declaration with an intentionally wrong registered type OID. -/
abbrev Item := Nat

end Fixture
