import LatticeSystem.Quantum.SpinS.AllAlignedAddNeelExpectationEqZero
import LatticeSystem.Quantum.SpinS.AllUpExpectationReNonneg

/-!
# `⟨Φ_Néel⟩.re ≤ 0` unconditionally

Direct from PR #3198 (`⟨Φ_↑⟩.re + ⟨Φ_Néel⟩.re = 0`) + PR #3240
(`0 ≤ ⟨Φ_↑⟩.re`):

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re ≤ 0`

unconditionally. Concretely `−|A|·|¬A|·N²/2 ≤ 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_Néel⟩.re ≤ 0`** unconditionally. -/
theorem heisenbergToyHamiltonianS_neel_expectation_re_nonpos
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ≤ 0 := by
  have h1 := heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_nonneg
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h1
  linarith

end LatticeSystem.Quantum
