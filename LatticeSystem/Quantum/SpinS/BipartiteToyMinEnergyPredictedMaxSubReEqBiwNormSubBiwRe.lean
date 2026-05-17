import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubAvgEqBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqAvgAddBiwNorm

/-!
# `max(...) − (pmA).re = ‖biw‖ − biw.re` unconditionally

The orientation-pair max minus the canonical predicted-min energy
equals `‖biw‖ − biw.re`:

  `max((pmA).re, (pm¬A).re) − (predicted_min A).re = ‖biw‖ − biw.re`

unconditionally. Combines PR #3125 (`max = avg + ‖biw‖`) with PR #3157
(`(pmA).re − avg = biw.re`) via linarith.

Matches PR #3161 (`predictedSymm.re − (pmA).re = ‖biw‖ − biw.re`)
since `predictedSymm = max` by PR #3001.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(...) − (pmA).re = ‖biw‖ − biw.re`** unconditionally. Explicit max-form of PR #3161. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_sub_re_eq_biw_norm_sub_biw_re
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := bipartiteToyMinEnergyPredicted_re_sub_avg_complement_re_eq_biw_re
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_max_complement_re_eq_avg_add_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
