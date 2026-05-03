import LatticeSystem.Fermion.AnnihilationCreationIdentity
import LatticeSystem.Fermion.NumberSpinSBridge

/-!
# `c · c† = (1/2) · I + spinSOp3 1` at spin-`S` (`N = 1`)

Combines PRs #937 and #963 to express the hole occupation operator
`c · c†` in spin-`S` form:

  `c · c† = 1 − n = 1 − ((1/2) · I − Ŝ^(3)) = (1/2) · I + Ŝ^(3)`.

Standard physics identification mirroring `n = (I − σ^z)/2`.

Tracked as part of Tasaki §2.4 / §2.5 / Phase 2 fermion infrastructure
(Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `c · c† = (1/2) • 1 + spinSOp3 1`. -/
theorem fermionAnnihilation_mul_fermionCreation_eq_half_smul_one_add_spinSOp3_one :
    fermionAnnihilation * fermionCreation =
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        LatticeSystem.Quantum.spinSOp3 1 := by
  rw [fermionAnnihilation_mul_fermionCreation_eq_one_sub_number]
  rw [fermionNumber_eq_half_smul_one_sub_spinSOp3_one]
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        LatticeSystem.Quantum.spinSOp3 1) =
      ((1 : ℂ) - (1 / 2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        LatticeSystem.Quantum.spinSOp3 1 from by
    rw [sub_smul, one_smul]
    abel]
  congr 1
  · norm_num

end LatticeSystem.Fermion
