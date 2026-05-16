import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# `(pmA).re < (pm¬A).re ↔ |A| < |¬A|` at `N ≥ 1`

PR #3021: `(pmA).re − (pm¬A).re = (|A| − |¬A|)·N`. At `N ≥ 1`:

  `(predicted_min A).re < (predicted_min ¬A).re ↔ |A| < |¬A|`.

The canonical orientation strictly fails to be the minimum exactly
when complement-sublattice dominates.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re < (pm¬A).re iff `|A| < |¬A|`** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_re_lt_complement_re_iff_cardA_lt_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hdiff := bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq (Λ := Λ) A N
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro hlt
    have hprod_neg : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) < 0 := by
      linarith
    have hsub_neg : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) < 0 := by
      by_contra hnn
      push Not at hnn
      have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) ≥ 0 :=
        mul_nonneg hnn (le_of_lt hN_re)
      linarith
    have hcA_lt_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
    exact_mod_cast hcA_lt_re
  · intro hcard_lt
    have hcA_lt_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcard_lt
    have hsub_neg : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) < 0 := by linarith
    have hprod_neg : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hsub_neg hN_re
    linarith

end LatticeSystem.Quantum
