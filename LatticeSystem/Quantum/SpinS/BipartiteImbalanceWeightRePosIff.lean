import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `biw.re > 0 ↔ |¬A| < |A| ∧ 0 < N`

`biw.re = (|A| − |¬A|) · N / 2`. Strict positivity iff both `(|A| − |¬A|) > 0`
and `N > 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re > 0 iff `|¬A| < |A| ∧ 0 < N`**. -/
theorem bipartiteImbalanceWeight_re_pos_iff
    (A : Λ → Bool) (N : ℕ) :
    0 < (bipartiteImbalanceWeight (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < N := by
  rw [bipartiteImbalanceWeight_re_eq]
  constructor
  · intro hlt
    have hsplit : 0 <
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) ∧
        0 < ((N : ℝ) / 2) := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      rcases lt_or_eq_of_le hN_nn with hN_pos | hN_zero
      · -- N > 0.
        constructor
        · -- prod positive and N positive → factor positive.
          by_contra hnon
          push Not at hnon
          have hN_div : (0 : ℝ) < (N : ℝ) / 2 := by positivity
          have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
              ((N : ℝ) / 2) ≤ 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg hnon hN_div.le
          linarith
        · positivity
      · -- N = 0, contradicts hlt.
        have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
            ((N : ℝ) / 2) = 0 := by
          rw [← hN_zero]; ring
        linarith
    obtain ⟨hdiff, hN⟩ := hsplit
    refine ⟨?_, ?_⟩
    · -- |¬A| < |A| from diff > 0.
      have : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) <
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by linarith
      exact_mod_cast this
    · -- N > 0 from N/2 > 0.
      have : (0 : ℝ) < (N : ℝ) := by linarith
      exact_mod_cast this
  · intro ⟨hcard, hN⟩
    have hcard_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      exact_mod_cast hcard
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdiff_pos : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
    have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
    exact mul_pos hdiff_pos hhalf_pos

end LatticeSystem.Quantum
