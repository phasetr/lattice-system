import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# `max(...) = (predicted_min ¬A).re` at complement orientation `|A| ≤ |¬A|`

Mirror of PR #3048. At complement orientation `|A| ≤ |¬A|`: `(pmA).re
≤ (pm¬A).re`, so the max is realised by the complement orientation:

  `|A| ≤ |¬A| → max((predicted_min A).re, (predicted_min ¬A).re)
   = (predicted_min ¬A).re`

unconditionally in `N`. Consistent with PR #3010 (`pm(¬A).re =
predictedSymm.re ↔ |A| ≤ |¬A|`) via PR #3001.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **max identification at complement orientation**: `|A| ≤ |¬A| →
max(...) = (predicted_min ¬A).re`. Mirror of PR #3048. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_eq_complement_at_complement
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
  have hdiff := bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq (Λ := Λ) A N
  have hle_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by exact_mod_cast h
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpm_le : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
    have hprod_np : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact hNnn
    linarith
  exact max_eq_right hpm_le

end LatticeSystem.Quantum
