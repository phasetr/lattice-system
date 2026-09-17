module

public import Init

@[expose] public section

namespace Fixture

/-- A structure used to measure and lock generated declaration ownership. -/
structure Pair where
  /-- First fixture field. -/
  left : Nat
  /-- Second fixture field. -/
  right : Nat

end Fixture
