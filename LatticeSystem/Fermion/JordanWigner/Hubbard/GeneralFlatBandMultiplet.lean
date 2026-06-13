import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandTwoHoleCollapse
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral

/-!
# The general flat-band maximal-spin multiplet (Tasaki §11.3.4)

The ground subspace of a connected general flat-band Hubbard model is the `(D₀+1)`-fold maximal-spin
multiplet.  The all-up μ-Slater state `Slater(canonical I (fun _ => 0))` is the highest-weight
vector (`Ŝ⁺_tot` annihilates it, `Ŝᶻ_tot` eigenvalue `D₀/2`); the SU(2) lowering tower
`highestWeight_spinMultiplet_general` then produces `D₀+1` linearly independent ground states all
carrying total spin `(D₀/2)(D₀/2+1)`, which (with the `finrank ≤ D₀+1` upper bound
`generalFlatBandGround_finrank_le_of_connected`) pins the ground subspace as the multiplet.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4, Theorem 11.17, pp. 410–412.  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {M : ℕ}

/-- **`Ŝ⁺_tot` annihilates the all-up μ-Slater state**: `Ŝ⁺_tot = Σ_i ĉ†_{i,↑}ĉ_{i,↓}` and each
down-annihilation `ĉ_{i,↓}` kills the all-up Slater (every creation mode carries spin `↑ = 0 ≠ 1`),
so the whole raising operator does.  This is the highest-weight condition `Ŝ⁺ v = 0` for the SU(2)
tower of the general flat-band ferromagnet. -/
theorem generalFlatBand_totalSpinPlus_mulVec_allUpSlater (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (I : Finset (Fin (M + 1))) :
    (fermionTotalSpinPlus M).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
  unfold fermionTotalSpinPlus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Matrix.mulVec_mulVec]
  have hdown : (fermionDownAnnihilation M i).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
    rw [fermionDownAnnihilation]
    refine generalFlatBand_siteAnnihilation_eq_zero μ i 1 _ (fun q hq => Or.inr ?_)
    rw [flatBandSpinConfigList_mem_snd_eq I (fun _ => 0) hq]
    decide
  rw [hdown, Matrix.mulVec_zero]

end LatticeSystem.Fermion
