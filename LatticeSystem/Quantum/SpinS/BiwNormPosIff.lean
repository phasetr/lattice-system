import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# iff: `0 < ‖biw‖ ↔ |A| ≠ |¬A| ∧ 0 < N`

The imbalance-weight norm is strictly positive exactly when the
orientation pair is unbalanced and `N` is positive.

  `0 < ‖biw‖ ↔ |A| ≠ |¬A| ∧ 0 < N`

unconditionally. From `‖biw‖ = ||A|−|¬A||·N/2`, which is strictly
positive iff `||A|−|¬A|| > 0` and `N > 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 < ‖biw‖ iff `|A| ≠ |¬A| ∧ 0 < N`**. -/
theorem bipartiteImbalanceWeight_norm_pos_iff
    (A : Λ → Bool) (N : ℕ) :
    0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧ 0 < N := by
  rw [bipartiteImbalanceWeight_norm_eq]
  constructor
  · intro hpos
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have h_abs_nn : (0 : ℝ) ≤
        |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| := abs_nonneg _
    rcases lt_or_eq_of_le hN_nn with hN_pos | hN_zero
    · have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
      have h_abs_pos : (0 : ℝ) < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| := by
        by_contra hz
        push Not at hz
        have h_abs_zero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| = 0 :=
          le_antisymm hz h_abs_nn
        rw [h_abs_zero] at hpos
        simp at hpos
      have h_card_ne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≠
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        intro h
        rw [h, sub_self, abs_zero] at h_abs_pos
        exact lt_irrefl _ h_abs_pos
      refine ⟨?_, ?_⟩
      · intro h_eq
        apply h_card_ne
        exact_mod_cast h_eq
      · exact_mod_cast hN_pos
    · have hN_re : (N : ℝ) = 0 := hN_zero.symm
      have : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
          ((N : ℝ) / 2) = 0 := by rw [hN_re]; ring
      linarith
  · intro ⟨hcard_ne, hN⟩
    have h_card_re_ne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≠
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      intro h
      apply hcard_ne
      exact_mod_cast h
    have h_abs_pos : (0 : ℝ) < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| :=
      abs_pos.mpr (sub_ne_zero.mpr h_card_re_ne)
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
    exact mul_pos h_abs_pos hhalf_pos

end LatticeSystem.Quantum
