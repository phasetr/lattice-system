import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyNonpos
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `max((pmA).re, (pm¬A).re) ≤ 0` unconditionally

PR #2791: `(predicted_min A).re ≤ 0` unconditionally.

Applying PR #2791 to both `A` and `¬A` (mirror of PR #3029):

  `max((predicted_min A).re, (predicted_min ¬A).re) ≤ 0`

unconditionally.

Since `max = predictedSymm` (PR #3001), this is equivalent to PR #2844
(`(predictedSymm A).re ≤ 0`), but stated in the `max` form for direct
use with the orientation-spread framework.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Max of orientation-specific predicted min energies is non-positive**:
unconditional. Direct from PR #2791 applied to both orientations. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_le_zero
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤ 0 :=
  max_le (bipartiteToyMinEnergyPredicted_re_nonpos (Λ := Λ) A N)
    (bipartiteToyMinEnergyPredicted_re_nonpos (Λ := Λ) (fun x => ! A x) N)

end LatticeSystem.Quantum
