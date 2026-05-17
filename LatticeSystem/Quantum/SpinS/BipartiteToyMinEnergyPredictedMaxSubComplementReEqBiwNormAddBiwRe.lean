import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementReSubAvgEqNegBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqAvgAddBiwNorm

/-!
# `max(...) − (pm¬A).re = ‖biw‖ + biw.re` unconditionally

Mirror of PR #3188. The orientation-pair max minus the complement
predicted-min energy equals `‖biw‖ + biw.re`:

  `max((pmA).re, (pm¬A).re) − (predicted_min ¬A).re = ‖biw‖ + biw.re`

unconditionally. Combines PR #3125 (`max = avg + ‖biw‖`) with PR #3158
(`(pm¬A).re − avg = −biw.re`) via linarith. Matches PR #3162 form via
PR #3001 (`max = predictedSymm.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(...) − (pm¬A).re = ‖biw‖ + biw.re`** unconditionally. Mirror of PR #3188. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_sub_complement_re_eq_biw_norm_add_biw_re
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := bipartiteToyMinEnergyPredicted_complement_re_sub_avg_complement_re_eq_neg_biw_re
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_max_complement_re_eq_avg_add_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
