import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubCanonicalPredicted

/-!
# iff: `0 < ⟨Néel⟩.re − (pmA).re ↔ 0 < |¬A| ∧ 0 < N`

The Néel-state expectation minus the canonical-orientation predicted
min energy is strictly positive exactly when the complement is
non-empty and `N` is positive:

  `0 < ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − (predicted_min A).re ↔ 0 < |¬A| ∧ 0 < N`.

Uses the explicit gap formula `⟨Néel⟩.re − (pmA).re = |¬A|·N` from
existing PR `NeelStateOfSExpectationSubCanonicalPredicted.lean`, then
`|¬A|·N > 0 ↔ |¬A| > 0 ∧ N > 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < ⟨Néel⟩.re − (pmA).re iff `0 < |¬A| ∧ 0 < N`**. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_pos_iff
    (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ↔
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧ 0 < N := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq]
  constructor
  · intro hpos
    -- |¬A|·N > 0 → both > 0.
    have hNotA_nn : (0 : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
      Nat.cast_nonneg _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    rcases lt_or_eq_of_le hN_nn with hN_pos | hN_zero
    · have hNotA_pos : (0 : ℝ) <
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        by_contra hz
        push Not at hz
        have hNotA_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 :=
          le_antisymm hz hNotA_nn
        rw [hNotA_zero] at hpos
        simp at hpos
      refine ⟨?_, ?_⟩
      · exact_mod_cast hNotA_pos
      · exact_mod_cast hN_pos
    · -- N = 0 → product 0, contradicts hpos.
      have : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) = 0 := by
        rw [← hN_zero]; ring
      linarith
  · intro ⟨hNotA, hN⟩
    have hNotA_re : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hNotA
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact mul_pos hNotA_re hN_re

end LatticeSystem.Quantum
