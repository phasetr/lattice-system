import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg

/-!
# iff: `0 < ⟨Néel⟩.re − avg ↔ 0 < |Λ| ∧ 0 < N`

The Néel-state expectation minus the orientation-pair average is
strictly positive exactly when `Λ` is non-empty and `N` is positive.

  `0 < ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − avg ↔ 0 < |Λ| ∧ 0 < N`.

Uses the explicit gap formula `⟨Néel⟩.re − avg = |Λ|·N/2` (PR #3051).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < ⟨Néel⟩.re − avg iff `0 < |Λ| ∧ 0 < N`**. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_pos_iff
    (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      0 < Fintype.card Λ ∧ 0 < N := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq]
  -- |Λ|·N/2 > 0 iff |Λ| > 0 ∧ N > 0.
  constructor
  · intro hpos
    have hΛ_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := Nat.cast_nonneg _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    rcases lt_or_eq_of_le hN_nn with hN_pos | hN_zero
    · have hΛ_pos : (0 : ℝ) < (Fintype.card Λ : ℝ) := by
        by_contra hz
        push Not at hz
        have hΛ_zero : (Fintype.card Λ : ℝ) = 0 := le_antisymm hz hΛ_nn
        rw [hΛ_zero] at hpos
        simp at hpos
      refine ⟨?_, ?_⟩
      · exact_mod_cast hΛ_pos
      · exact_mod_cast hN_pos
    · have : (Fintype.card Λ : ℝ) * (N : ℝ) / 2 = 0 := by
        rw [← hN_zero]; ring
      linarith
  · intro ⟨hΛ, hN⟩
    have hΛ_re : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hΛN_pos : (0 : ℝ) < (Fintype.card Λ : ℝ) * (N : ℝ) := mul_pos hΛ_re hN_re
    linarith

end LatticeSystem.Quantum
