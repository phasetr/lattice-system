import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# `max(...) = (predicted_min A).re` at proper orientation `|¬A| ≤ |A|`

PR #3021: `(pmA).re − (pm¬A).re = (|A| − |¬A|)·N`.

At proper orientation `|¬A| ≤ |A|`: `(pmA).re ≥ (pm¬A).re`, hence
the max is achieved by the canonical orientation:

  `|¬A| ≤ |A| → max((predicted_min A).re, (predicted_min ¬A).re)
   = (predicted_min A).re`

unconditionally in `N`. Mirror of PR #3046 for the max side. Together
with PR #3001 (max = predictedSymm), this is consistent with PR #3009
(`(pmA).re = (predictedSymm A).re` at proper orientation).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **max identification at proper orientation**: `|¬A| ≤ |A| →
max(...) = (predicted_min A).re`. Mirror of PR #3046. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_eq_canonical_at_proper
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
  have hdiff := bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq (Λ := Λ) A N
  have hle_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by exact_mod_cast h
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpm_ge : (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
    have hprod_nn : 0 ≤ (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) := by
      apply mul_nonneg
      · linarith
      · exact hNnn
    linarith
  exact max_eq_left hpm_ge

end LatticeSystem.Quantum
