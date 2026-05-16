import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubAvgEqHalfSpread
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `avg = (predictedSymm A).re − ‖biw‖`

PR #3034: `(predictedSymm A).re − avg = ||A| − |¬A||·N / 2`.
`bipartiteImbalanceWeight_norm_eq`: `‖biw‖ = ||A| − |¬A||·N/2`.

Combining:

  `((pmA).re + (pm¬A).re) / 2 = (predictedSymm A).re − ‖biw‖`

unconditionally. Expresses avg as predictedSymm minus the imbalance-
weight norm.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg = predictedSymm.re − ‖biw‖** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_eq_predictedSymm_re_sub_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have hgap := bipartiteToyMinEnergyPredictedSymm_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  rw [bipartiteImbalanceWeight_norm_eq A N]
  linarith

end LatticeSystem.Quantum
