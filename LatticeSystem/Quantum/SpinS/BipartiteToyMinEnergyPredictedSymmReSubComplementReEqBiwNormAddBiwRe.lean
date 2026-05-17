import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqAvgAddBiwNorm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementReSubAvgEqNegBiwRe

/-!
# `predictedSymm.re − (pm¬A).re = ‖biw‖ + biw.re` unconditionally

Mirror of PR #3161. The gap between the symmetric predicted-min energy
and the complement orientation's predicted-min energy equals the sum
of the imbalance-weight's norm and its (signed) real part:

  `predictedSymm.re − (pm¬A).re = ‖biw‖ + biw.re`

unconditionally. Composes PR #3001 (`max = predictedSymm.re`) +
PR #3125 (`max = avg + ‖biw‖`) + PR #3158 (`(pm¬A).re − avg = −biw.re`).

Concretely:
- At `|A| ≥ |¬A|` (so `biw.re ≥ 0` and `‖biw‖ = biw.re`):
  `‖biw‖ + biw.re = 2 · biw.re ≥ 0`, with equality only at balanced.
- At `|A| < |¬A|` (so `biw.re < 0` and `‖biw‖ = −biw.re`):
  `‖biw‖ + biw.re = 0`, i.e. the complement orientation already attains
  the symmetric max.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`predictedSymm.re − (pm¬A).re = ‖biw‖ + biw.re`** unconditionally. Mirror of PR #3161. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_sub_complement_re_eq_biw_norm_add_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_avg_add_biw_norm A N]
  -- (pm¬A).re = avg − biw.re by PR #3158.
  have h := bipartiteToyMinEnergyPredicted_complement_re_sub_avg_complement_re_eq_neg_biw_re
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
