import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqAvgAddBiwNorm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubAvgEqBiwRe

/-!
# `predictedSymm.re − (pmA).re = ‖biw‖ − biw.re` unconditionally

The gap between the symmetric predicted-min energy and the canonical
orientation's predicted-min energy equals the difference between the
imbalance-weight's norm and its (signed) real part:

  `predictedSymm.re − (pmA).re = ‖biw‖ − biw.re`

unconditionally. Composes PR #3001 (`max = predictedSymm.re`) +
PR #3125 (`max = avg + ‖biw‖`) + PR #3157 (`(pmA).re − avg = biw.re`).

Concretely:
- At `|A| ≥ |¬A|` (so `biw.re ≥ 0` and `‖biw‖ = biw.re`):
  `‖biw‖ − biw.re = 0`, i.e. the canonical orientation already attains
  the symmetric max.
- At `|A| < |¬A|` (so `biw.re < 0` and `‖biw‖ = −biw.re`):
  `‖biw‖ − biw.re = −2 · biw.re > 0`, so the symmetric max is achieved
  by the complement orientation `pm¬A`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`predictedSymm.re − (pmA).re = ‖biw‖ − biw.re`** unconditionally. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_sub_re_eq_biw_norm_sub_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  -- predictedSymm.re = max(pmA, pm¬A) = avg + ‖biw‖.
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_avg_add_biw_norm A N]
  -- (pmA).re = avg + biw.re by PR #3157.
  have h := bipartiteToyMinEnergyPredicted_re_sub_avg_complement_re_eq_biw_re
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
