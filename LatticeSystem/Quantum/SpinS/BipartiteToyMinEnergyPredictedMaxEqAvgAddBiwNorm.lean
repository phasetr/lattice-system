import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgEqSymmSubBiwNorm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `max(...) = avg + ‖biw‖`

PR #3123: `avg = (predictedSymm A).re − ‖biw‖`.
PR #3001: `max = (predictedSymm A).re`.

Combining:

  `max((pmA).re, (pm¬A).re) = avg + ‖biw‖`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **max = avg + ‖biw‖** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_eq_avg_add_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N,
      bipartiteToyMinEnergyPredicted_avg_complement_re_eq_predictedSymm_re_sub_biw_norm A N]
  ring

end LatticeSystem.Quantum
