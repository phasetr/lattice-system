import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `spread = 2 · ‖biw‖`

The orientation-pair spread equals twice the imbalance-weight norm:

  `max((pmA).re, (pm¬A).re) − min((pmA).re, (pm¬A).re) = 2 · ‖biw‖`

unconditionally. Direct from PR #3012 (spread = `||A| − |¬A||·N`)
and the existing biw norm formula `‖biw‖ = ||A| − |¬A||·N/2`.

Connects the orientation-spread to the Tasaki §2.5 Theorem 2.3
imbalance weight: the spread is twice the predicted total-spin norm.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Spread = 2 · ‖biw‖** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_two_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq A N,
      bipartiteImbalanceWeight_norm_eq A N]
  ring

end LatticeSystem.Quantum
