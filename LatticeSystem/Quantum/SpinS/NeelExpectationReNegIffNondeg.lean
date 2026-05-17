import LatticeSystem.Quantum.SpinS.AllAlignedAddNeelExpectationEqZero
import LatticeSystem.Quantum.SpinS.AllUpExpectationRePosIffNondeg

/-!
# iff: `⟨Φ_Néel⟩.re < 0 ↔ nondeg`

The Néel state's toy-Hamiltonian expectation is strictly negative
exactly at non-degenerate. Combines PR #3198 (`⟨Φ_↑⟩ + ⟨Φ_Néel⟩ = 0`)
with PR #3245 (`0 < ⟨Φ_↑⟩.re ↔ nondeg`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_Néel⟩.re < 0 iff nondeg`** unconditionally. -/
theorem heisenbergToyHamiltonianS_neel_expectation_re_neg_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re < 0 ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  have h_sum := heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h_sum
  have h_up_pos := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_pos_iff_nondeg
    (Λ := Λ) (A := A) (N := N)
  constructor
  · intro hneg
    -- Néel < 0 → allUp = -Néel > 0 → nondeg.
    have h_up_pos_val : 0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re := by linarith
    exact h_up_pos.mp h_up_pos_val
  · intro hor
    have h_up_pos_val : 0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re := h_up_pos.mpr hor
    linarith

end LatticeSystem.Quantum
