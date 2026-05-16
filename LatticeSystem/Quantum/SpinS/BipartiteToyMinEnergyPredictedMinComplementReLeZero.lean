import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyNonpos
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `min((pmA).re, (pm¬A).re) ≤ 0` unconditionally

PR #2791: `(predicted_min A).re ≤ 0` unconditionally.

Applying PR #2791 to both `A` and `¬A` and taking the min:

  `min((predicted_min A).re, (predicted_min ¬A).re) ≤ 0`

unconditionally.

Companion of the unconditional non-positivity bounds — convenient
when working with the min form of the orientation pair.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Min of orientation-specific predicted min energies is non-positive**:
unconditional. Direct from PR #2791 applied to both orientations. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_le_zero
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤ 0 :=
  min_le_of_left_le (bipartiteToyMinEnergyPredicted_re_nonpos (Λ := Λ) A N)

end LatticeSystem.Quantum
