module

public import Mathlib.FixtureDependency

@[expose] public section

namespace Fixture

/-- Depends transitively, but not directly, on sorryAx. -/
def Item : Nat := Mathlib.hidden

end Fixture
