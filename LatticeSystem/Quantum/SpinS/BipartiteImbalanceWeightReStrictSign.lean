import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Strict sign of `bipartiteImbalanceWeight` real part

PR #2773 proved `_re_nonneg_of_cardA_ge_cardNotA`. This file adds
the strict-inequality variants:

- `_re_pos_of_cardA_gt_cardNotA_of_N_pos`:
  `|A| > |¬A|` and `N ≥ 1` imply `(bipartiteImbalanceWeight A N).re > 0`.
- `_re_neg_of_cardA_lt_cardNotA_of_N_pos`:
  `|A| < |¬A|` and `N ≥ 1` imply `(bipartiteImbalanceWeight A N).re < 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **Strict positivity of `bipartiteImbalanceWeight.re` for
strict majority `|A| > |¬A|` and `N ≥ 1`**:
`(bipartiteImbalanceWeight A N).re > 0`. -/
theorem bipartiteImbalanceWeight_re_pos_of_cardA_gt_cardNotA_of_N_pos
    (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    0 < (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteImbalanceWeight_re_eq]
  have hdiff : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    have : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
      by exact_mod_cast h
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  exact mul_pos hdiff hN_pos

/-- **Strict negativity of `bipartiteImbalanceWeight.re` for
strict minority `|A| < |¬A|` and `N ≥ 1`**:
`(bipartiteImbalanceWeight A N).re < 0`. -/
theorem bipartiteImbalanceWeight_re_neg_of_cardA_lt_cardNotA_of_N_pos
    (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card <
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re < 0 := by
  rw [bipartiteImbalanceWeight_re_eq]
  have hdiff :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) < 0 := by
    have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
      by exact_mod_cast h
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  exact mul_neg_of_neg_of_pos hdiff hN_pos

end LatticeSystem.Quantum
