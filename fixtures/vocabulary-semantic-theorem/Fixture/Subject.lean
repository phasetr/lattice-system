module

public import Init

@[expose] public section

namespace Fixture

/-- An intentionally forbidden theorem in a vocabulary module. -/
theorem Item : True := trivial

end Fixture
