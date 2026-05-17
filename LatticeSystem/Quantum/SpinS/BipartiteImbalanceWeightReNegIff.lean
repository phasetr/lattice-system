import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `biw.re < 0 ↔ |A| < |¬A| ∧ 0 < N`

Mirror of PR #3151. `biw.re = (|A| − |¬A|) · N / 2`. Strict negativity
iff both `(|A| − |¬A|) < 0` and `N > 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re < 0 iff `|A| < |¬A| ∧ 0 < N`**. Mirror of PR #3151. -/
theorem bipartiteImbalanceWeight_re_neg_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re < 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  rw [bipartiteImbalanceWeight_re_eq]
  constructor
  · intro hlt
    -- Split: factor of (|A| − |¬A|) negative and (N/2) positive.
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    rcases lt_or_eq_of_le hN_nn with hN_pos | hN_zero
    · -- N > 0 case.
      have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
      have hdiff_neg : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) < 0 := by
        by_contra hnonneg
        push Not at hnonneg
        have hge : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
            ((N : ℝ) / 2) ≥ 0 :=
          mul_nonneg hnonneg hhalf_pos.le
        linarith
      refine ⟨?_, ?_⟩
      · have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) <
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
          linarith
        exact_mod_cast hcard_re
      · exact_mod_cast hN_pos
    · -- N = 0 case → biw.re = 0, contradicting hlt.
      have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
          ((N : ℝ) / 2) = 0 := by
        rw [← hN_zero]; ring
      linarith
  · intro ⟨hcard, hN⟩
    have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcard
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdiff_neg : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) < 0 := by linarith
    have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
    exact mul_neg_of_neg_of_pos hdiff_neg hhalf_pos

end LatticeSystem.Quantum
