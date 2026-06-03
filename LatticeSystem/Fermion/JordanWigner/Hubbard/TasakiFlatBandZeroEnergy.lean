import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandGroundState

/-!
# Tasaki §11.3.1: the all-up `α` state is a zero-energy state of `Ĥ` (toward Thm 11.11)

`|Φα,all↑⟩` has no down-electrons, so every down annihilation kills it; hence the
on-site interaction `Ĥ_int = U Σ_x n̂_{x↑} n̂_{x↓}` annihilates it
(`flatBandHamiltonian_int_mulVec_alphaAllUpState`).  Combined with the merged
`Ĥ_hop |Φα,all↑⟩ = 0`, the full flat-band Hamiltonian annihilates `|Φα,all↑⟩`
(`flatBandHamiltonian_mulVec_alphaAllUpState`): since `Ĥ = Ĥ_hop + Ĥ_int` is a sum
of positive-semidefinite terms, `|Φα,all↑⟩` is a zero-energy ground state.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11 (existence half).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- A down annihilation operator anticommutes with the up `â†` operators:
`{ĉ_{x,↓}, â†_{p,↑}} = 0` (different spin). -/
theorem flatBandCDownAnnihilation_ACreation_anticomm (K : ℕ) (ν : ℝ)
    (x : Fin (2 * K + 2)) (p : Fin (K + 1)) :
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1) *
        flatBandACreation K ν p 0
      + flatBandACreation K ν p 0 *
        fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1) = 0 := by
  unfold flatBandACreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun y _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, spinful_annihilation_creation_anticomm,
    if_neg (fun h => absurd h.2 (by decide)), smul_zero]

/-- `ĉ_{x,↓}` annihilates the all-up `α` state (it has no down electrons). -/
theorem flatBandCDownAnnihilation_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ)
    (x : Fin (2 * K + 2)) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1)).mulVec
      (flatBandAlphaAllUpState K ν) = 0 := by
  unfold flatBandAlphaAllUpState
  rw [Matrix.mulVec_mulVec]
  exact flatBand_anticomm_listProd_mulVec_vacuum
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1))
    (fun p => flatBandACreation K ν p 0) (List.finRange (K + 1))
    (fermionMultiAnnihilation_mulVec_vacuum _ _)
    (fun p _ => flatBandCDownAnnihilation_ACreation_anticomm K ν x p)

/-- The on-site double-occupancy operator annihilates the all-up `α` state. -/
theorem hubbardDoubleOccupancy_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ)
    (x : Fin (2 * K + 2)) :
    (hubbardDoubleOccupancy (2 * K + 1) x).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  have hdown : (fermionDownNumber (2 * K + 1) x).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
    unfold fermionDownNumber fermionMultiNumber
    rw [← Matrix.mulVec_mulVec, flatBandCDownAnnihilation_mulVec_alphaAllUpState,
      Matrix.mulVec_zero]
  unfold hubbardDoubleOccupancy
  rw [← Matrix.mulVec_mulVec, hdown, Matrix.mulVec_zero]

/-- `Ĥ_int |Φα,all↑⟩ = 0`. -/
theorem flatBandHamiltonian_int_mulVec_alphaAllUpState (K : ℕ) (ν U : ℝ) :
    ((U : ℂ) • ∑ x : Fin (2 * K + 2), hubbardDoubleOccupancy (2 * K + 1) x).mulVec
      (flatBandAlphaAllUpState K ν) = 0 := by
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec,
    Finset.sum_eq_zero (fun x _ => hubbardDoubleOccupancy_mulVec_alphaAllUpState K ν x),
    smul_zero]

/-- **`Ĥ |Φα,all↑⟩ = 0`**: the all-up `α` state is a zero-energy state of the full
flat-band Hamiltonian (`Ĥ_hop` and `Ĥ_int` both annihilate it). -/
theorem flatBandHamiltonian_mulVec_alphaAllUpState (K : ℕ) (ν t U : ℝ) :
    (flatBandHamiltonian K ν t U).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold flatBandHamiltonian
  rw [Matrix.add_mulVec]
  have hhop := flatBandHopping_mulVec_alphaAllUpState K ν t
  unfold flatBandHopping at hhop
  rw [hhop, flatBandHamiltonian_int_mulVec_alphaAllUpState, add_zero]

end LatticeSystem.Fermion
