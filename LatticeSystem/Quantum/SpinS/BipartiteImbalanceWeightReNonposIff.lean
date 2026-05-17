import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `biw.re ≤ 0 ↔ |A| ≤ |¬A| ∨ N = 0`

Mirror of PR #3155. `biw.re = (|A| − |¬A|) · N / 2` is ≤ 0 iff
the cardinality difference is non-positive OR `N = 0`.

Companion to PRs #3151/#3152/#3153/#3155 — together completing the
sign classification of `biw.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re ≤ 0 iff `|A| ≤ |¬A| ∨ N = 0`**. Mirror of PR #3155. -/
theorem bipartiteImbalanceWeight_re_nonpos_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  rw [bipartiteImbalanceWeight_re_eq]
  constructor
  · intro hnp
    by_cases hN_zero : N = 0
    · exact Or.inr hN_zero
    · left
      have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_zero
      have hN_re_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
      have hdiff_np : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤ 0 := by
        by_contra h
        push Not at h
        have : 0 < (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
            ((N : ℝ) / 2) :=
          mul_pos h hhalf_pos
        linarith
      have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
      exact_mod_cast hcard_re
  · intro hor
    rcases hor with hcard | hN
    · have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hcard
      have hdiff_np : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤ 0 := by linarith
      have hhalf_nn : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg hdiff_np hhalf_nn
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
          ((N : ℝ) / 2) = 0 := by rw [hN_re]; ring
      linarith

end LatticeSystem.Quantum
