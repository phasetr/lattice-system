import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubAvgEqBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinEqAvgSubBiwNorm

/-!
# `(pmA).re − min(...) = ‖biw‖ + biw.re` unconditionally

The canonical predicted-min energy minus the orientation-pair min
equals the sum of `‖biw‖` and `biw.re`:

  `(predicted_min A).re − min((pmA).re, (pm¬A).re) = ‖biw‖ + biw.re`

unconditionally. Combines PR #3157 (`(pmA).re − avg = biw.re`) with
PR #3126 (`min = avg − ‖biw‖`) via linarith.

Geometric content:
- At `|A| ≥ |¬A|` (so `min = (pm¬A).re`): gap = `2·biw.re ≥ 0`.
- At `|A| < |¬A|` (so `min = (pmA).re`): gap = 0.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re − min(...) = ‖biw‖ + biw.re`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_re_sub_min_complement_re_eq_biw_norm_add_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := bipartiteToyMinEnergyPredicted_re_sub_avg_complement_re_eq_biw_re
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_sub_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
