import LatticeSystem.Quantum.SpinS.AllDownVariationalGapReNonneg

/-!
# `⟨Φ_Néel⟩.re ≤ ⟨Φ_↓⟩.re` unconditionally

Packaged form of PR #3210 (`0 ≤ (⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re`):

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re ≤ ⟨Φ_↓|Ĥ_toy|Φ_↓⟩.re`

unconditionally. The Néel state always has expectation no greater than
the all-down state under the toy Hamiltonian.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_Néel⟩.re ≤ ⟨Φ_↓⟩.re`** unconditionally. Packaged form of PR #3210. -/
theorem heisenbergToyHamiltonianS_neel_expectation_re_le_all_down_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ≤
      (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re := by
  have h := heisenbergToyHamiltonianS_all_down_variational_gap_re_nonneg
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.sub_re] at h
  linarith

end LatticeSystem.Quantum
