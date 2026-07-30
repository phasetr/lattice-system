import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandGroundState
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Tasaki Theorem 11.11 support: particle number and the multiplet/ground submodules

This file provides supporting lemmas and definitions for Tasaki's flat-band
ferromagnetism theorem (§11.3.1, Theorem 11.11) in the half-filled sector
`N_e = |E| = K + 1`:

* `flatBandTotalNumber_commutator_ACreation` — `[N̂, â†_{p,↑}] = â†_{p,↑}`.
* `flatBandTotalNumber_mulVec_alphaAllUpState` — `N̂ |Φα,all↑⟩ = (K + 1) |Φα,all↑⟩`.
* `flatBandFerromagneticMultipletSubmodule` — the span of the `K + 2 = 2 S_max + 1`
  lowered states `(Ŝ^-_tot)^k |Φα,all↑⟩`.
* `flatBandHalfFilledGroundSubmodule` — the zero-energy (`ker Ĥ`) states in the
  `N_e = K + 1` particle-number sector.

The capstone theorem identifying these two submodules
(`flatBand_theorem_11_11_groundSubmodule_eq_multipletSpan`) is proved,
axiom-free, in `TasakiFlatBandClassification.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`[N̂, â†_{p,↑}] = â†_{p,↑}`**: the `α` creation raises the total particle
number by one (lifted termwise from `[N̂, c†_j] = c†_j`). -/
theorem flatBandTotalNumber_commutator_ACreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandACreation K ν p 0 =
      flatBandACreation K ν p 0 * fermionTotalNumber (2 * (2 * K + 1) + 1) +
        flatBandACreation K ν p 0 := by
  unfold flatBandACreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : fermionTotalNumber (2 * (2 * K + 1) + 1) *
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) =
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) *
        fermionTotalNumber (2 * (2 * K + 1) + 1) +
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) := by
    have h := fermionTotalNumber_commutator_fermionMultiCreation (2 * (2 * K + 1) + 1)
      (spinfulIndex (2 * K + 1) x 0)
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  rw [mul_smul_comm, smul_mul_assoc, hx, smul_add]

/-- **`N̂ |Φα,all↑⟩ = (K + 1) |Φα,all↑⟩`**: the all-up `α` state has exactly
`K + 1` particles (the half-filled flat band). -/
theorem flatBandTotalNumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVec (flatBandAlphaAllUpState K ν) =
      ((K + 1 : ℕ) : ℂ) • flatBandAlphaAllUpState K ν := by
  unfold flatBandAlphaAllUpState
  rw [Matrix.mulVec_mulVec,
    charge_listProd_mulVec_vacuum (fermionTotalNumber (2 * (2 * K + 1) + 1))
      (fun p => flatBandACreation K ν p 0) (List.finRange (K + 1))
      (fermionTotalNumber_mulVec_vacuum (2 * (2 * K + 1) + 1))
      (fun p _ => flatBandTotalNumber_commutator_ACreation K ν p),
    List.length_finRange]

/-- The ferromagnetic multiplet subspace: the span of the `K + 2 = 2 S_max + 1`
lowered states `(Ŝ^-_tot)^k |Φα,all↑⟩`. -/
noncomputable def flatBandFerromagneticMultipletSubmodule (K : ℕ) (ν : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (fun k : Fin (K + 2) =>
    ((fermionTotalSpinMinus (2 * K + 1)) ^ (k : ℕ)).mulVec
      (flatBandAlphaAllUpState K ν)))

/-- The half-filled flat-band ground subspace: the zero-energy (`ker Ĥ`) states in
the `N_e = K + 1` particle-number sector. -/
noncomputable def flatBandHalfFilledGroundSubmodule (K : ℕ) (ν t U : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  LinearMap.ker (flatBandHamiltonian K ν t U).mulVecLin ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVecLin
      ((K + 1 : ℕ) : ℂ)

end LatticeSystem.Fermion
