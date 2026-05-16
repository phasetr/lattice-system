import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# `min(...) = (predicted_min ¬A).re` at proper orientation `|¬A| ≤ |A|`

PR #3021: `(pmA).re − (pm¬A).re = (|A| − |¬A|)·N`.

At proper orientation `|¬A| ≤ |A|`: `|A| − |¬A| ≥ 0`, so `(pmA).re ≥
(pm¬A).re`. Hence the min is achieved by the complement orientation:

  `|¬A| ≤ |A| → min((predicted_min A).re, (predicted_min ¬A).re)
   = (predicted_min ¬A).re`

unconditionally in `N`. Identifies which orientation realises the
min on the proper side.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min identification at proper orientation**: `|¬A| ≤ |A| →
min(...) = (predicted_min ¬A).re`. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_complement_at_proper
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
  have hdiff := bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq (Λ := Λ) A N
  have hle_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by exact_mod_cast h
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpm_ge : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≥
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
    have hprod_nn : 0 ≤ (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) := by
      apply mul_nonneg
      · linarith
      · exact hNnn
    linarith
  exact min_eq_right hpm_ge

end LatticeSystem.Quantum
