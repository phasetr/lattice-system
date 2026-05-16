import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# `min(...) = (predicted_min A).re` at complement orientation `|A| ≤ |¬A|`

Mirror of PR #3046. At complement orientation `|A| ≤ |¬A|`:
`|A| − |¬A| ≤ 0`, so `(pmA).re ≤ (pm¬A).re`. Hence the min is
achieved by the canonical orientation:

  `|A| ≤ |¬A| → min((predicted_min A).re, (predicted_min ¬A).re)
   = (predicted_min A).re`

unconditionally in `N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min identification at complement orientation**: `|A| ≤ |¬A| →
min(...) = (predicted_min A).re`. Mirror of PR #3046. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_canonical_at_complement
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re := by
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
  exact min_eq_left hpm_le

end LatticeSystem.Quantum
