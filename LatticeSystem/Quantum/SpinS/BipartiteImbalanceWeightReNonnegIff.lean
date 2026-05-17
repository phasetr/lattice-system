import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `0 ≤ biw.re ↔ |¬A| ≤ |A| ∨ N = 0`

`biw.re = (|A| − |¬A|) · N / 2`. Non-strict non-negativity iff
the cardinality difference is non-negative OR `N = 0` (in which case
the product vanishes regardless of sign).

Companion to PR #3151 (strict positivity), PR #3152 (strict
negativity), PR #3153 (vanishing). Together with PR #3155 (non-strict
non-positivity), these complete the sign-classification of `biw.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ biw.re iff `|¬A| ≤ |A| ∨ N = 0`**. -/
theorem bipartiteImbalanceWeight_re_nonneg_iff
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card ∨
      N = 0 := by
  rw [bipartiteImbalanceWeight_re_eq]
  constructor
  · intro hnn
    by_cases hN_zero : N = 0
    · exact Or.inr hN_zero
    · -- N > 0 and product ≥ 0 → diff ≥ 0.
      left
      have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_zero
      have hN_re_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
      -- If diff < 0, product would be negative — contradiction.
      have hdiff_nn : (0 : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        by_contra h
        push Not at h
        have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
            ((N : ℝ) / 2) < 0 :=
          mul_neg_of_neg_of_pos h hhalf_pos
        linarith
      have hcard_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by linarith
      exact_mod_cast hcard_re
  · intro hor
    rcases hor with hcard | hN
    · have hcard_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
        exact_mod_cast hcard
      have hdiff_nn : (0 : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
      have hN_re_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      have hhalf_nn : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
      exact mul_nonneg hdiff_nn hhalf_nn
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
          ((N : ℝ) / 2) = 0 := by rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
