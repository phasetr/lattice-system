import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinEqAvgSubHalfSpread
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `min(...) = avg − ‖biw‖`

PR #3045: `min(...) = avg − ||A| − |¬A||·N/2`.
`bipartiteImbalanceWeight_norm_eq`: `‖biw‖ = ||A| − |¬A||·N/2`.

Combining:

  `min((pmA).re, (pm¬A).re) = avg − ‖biw‖`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min = avg − ‖biw‖** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_sub_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_sub_half_spread A N,
      bipartiteImbalanceWeight_norm_eq A N]
  ring

end LatticeSystem.Quantum
