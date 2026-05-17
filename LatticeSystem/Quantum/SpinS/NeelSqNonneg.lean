import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations

/-!
# `0 ≤ ⟨Φ_Néel⟩.re²` unconditionally

Packaged trivial inequality via `sq_nonneg`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ ⟨Φ_Néel⟩.re²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_neel_expectation_re_sq_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 :=
  sq_nonneg _

end LatticeSystem.Quantum
