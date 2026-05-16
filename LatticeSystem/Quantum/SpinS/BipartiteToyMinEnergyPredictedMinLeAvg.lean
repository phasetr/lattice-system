import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `min((pmA).re, (pm¬A).re) ≤ avg` unconditionally

For any two reals `x, y`, `min x y ≤ (x + y) / 2`. Hence:

  `min((predicted_min A).re, (predicted_min ¬A).re)
   ≤ ((predicted_min A).re + (predicted_min ¬A).re) / 2`

unconditionally. The arithmetic mean of any two reals lies between
their min and max. This is the lower companion of PR #3035
(`avg ≤ max = predictedSymm`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min ≤ avg** unconditional: the orientation-specific min sits
below the arithmetic mean of the two orientations. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_le_avg
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 := by
  have hmin_l : min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re :=
    min_le_left _ _
  have hmin_r : min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    min_le_right _ _
  linarith

end LatticeSystem.Quantum
