import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `0 ≤ ⟨Φ_↓⟩.re²` unconditionally

Packaged trivial inequality via `sq_nonneg`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ ⟨Φ_↓⟩.re²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_last_expectation_re_sq_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ^ 2 :=
  sq_nonneg _

end LatticeSystem.Quantum
