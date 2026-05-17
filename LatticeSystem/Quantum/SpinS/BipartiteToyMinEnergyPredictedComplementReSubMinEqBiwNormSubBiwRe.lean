import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementReSubAvgEqNegBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinEqAvgSubBiwNorm

/-!
# `(pm¬A).re − min(...) = ‖biw‖ − biw.re` unconditionally

Mirror of PR #3186. The complement predicted-min energy minus the
orientation-pair min equals `‖biw‖ − biw.re`:

  `(predicted_min ¬A).re − min((pmA).re, (pm¬A).re) = ‖biw‖ − biw.re`

unconditionally. Combines PR #3158 (`(pm¬A).re − avg = −biw.re`) with
PR #3126 (`min = avg − ‖biw‖`) via linarith.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(pm¬A).re − min(...) = ‖biw‖ − biw.re`** unconditionally. Mirror of PR #3186. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_sub_min_complement_re_eq_biw_norm_sub_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := bipartiteToyMinEnergyPredicted_complement_re_sub_avg_complement_re_eq_neg_biw_re
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_sub_biw_norm
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
