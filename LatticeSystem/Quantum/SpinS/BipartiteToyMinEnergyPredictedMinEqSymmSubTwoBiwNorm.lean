import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinEqSymmSubSpread
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `min(...) = (predictedSymm A).re − 2 · ‖biw‖`

PR #3032: `min(...) = (predictedSymm A).re − ||A| − |¬A||·N`.
`bipartiteImbalanceWeight_norm_eq`: `‖biw‖ = ||A| − |¬A||·N/2`.

Combining:

  `min((pmA).re, (pm¬A).re) = (predictedSymm A).re − 2 · ‖biw‖`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min = predictedSymm.re − 2 · ‖biw‖** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_predictedSymm_re_sub_two_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyMinEnergyPredicted_min_complement_re_eq_predictedSymm_re_sub_spread A N,
      bipartiteImbalanceWeight_norm_eq A N]
  ring

end LatticeSystem.Quantum
