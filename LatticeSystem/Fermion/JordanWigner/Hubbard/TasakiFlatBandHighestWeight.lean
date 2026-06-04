import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandZeroEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Tasaki §11.3.1: the all-up `α` state is a highest-weight maximal-spin state

Toward the existence half of Theorem 11.11 (flat-band ferromagnetism): the all-up
`α` Slater state `|Φα,all↑⟩ = (∏_p â†_{p,↑}) |vac⟩` is the SU(2) highest-weight
state of the ferromagnetic multiplet.  Concretely, with `N = 2K + 1` chain sites
and `|E| = K + 1` electrons:

* `Ŝ^+_tot |Φα,all↑⟩ = 0` (`flatBandTotalSpinPlus_mulVec_alphaAllUpState`): every
  down annihilation in `Ŝ^+_tot` already kills the all-up state;
* `N̂_↑ |Φα,all↑⟩ = (K + 1) |Φα,all↑⟩`
  (`flatBandTotalUpNumber_mulVec_alphaAllUpState`): each `â†_{p,↑}` raises the up
  count by one (charge move-through over the ordered product);
* `N̂_↓ |Φα,all↑⟩ = 0` (`flatBandTotalDownNumber_mulVec_alphaAllUpState`): no down
  electrons;
* hence `Ŝ^z_tot |Φα,all↑⟩ = ((K + 1)/2) |Φα,all↑⟩`
  (`flatBandTotalSpinZ_mulVec_alphaAllUpState`), the highest weight `m = L/2` with
  `L = K + 1 = |E|` — *not* the chain maximum `N/2 = (2K+1)/2`.

These are exactly the hypotheses (`Ŝ^+ v = 0`, `Ŝ^z v = (L/2) v`) of the general
highest-weight tower `highestWeight_spinMultiplet_general`; combined with
`|Φα,all↑⟩ ≠ 0` they will yield the `(K + 2)`-dimensional maximal-spin
ferromagnetic multiplet.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11 (existence half).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`Ŝ^+_tot |Φα,all↑⟩ = 0`.**  `Ŝ^+_tot = Σ_i ĉ†_{i,↑} ĉ_{i,↓}` and each down
annihilation `ĉ_{i,↓}` already annihilates the all-up state, so the whole raising
operator does. -/
theorem flatBandTotalSpinPlus_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalSpinPlus (2 * K + 1)).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold fermionTotalSpinPlus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Matrix.mulVec_mulVec]
  have hdown : (fermionDownAnnihilation (2 * K + 1) i).mulVec
      (flatBandAlphaAllUpState K ν) = 0 :=
    flatBandCDownAnnihilation_mulVec_alphaAllUpState K ν i
  rw [hdown, Matrix.mulVec_zero]

/-- The local down number operator annihilates the all-up `α` state (no down
electrons). -/
theorem flatBandDownNumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ)
    (i : Fin (2 * K + 2)) :
    (fermionDownNumber (2 * K + 1) i).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold fermionDownNumber fermionMultiNumber
  rw [← Matrix.mulVec_mulVec, flatBandCDownAnnihilation_mulVec_alphaAllUpState,
    Matrix.mulVec_zero]

/-- **`N̂_↓ |Φα,all↑⟩ = 0`.**  Sum of the local down number operators, each of
which annihilates the all-up state. -/
theorem flatBandTotalDownNumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalDownNumber (2 * K + 1)).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => flatBandDownNumber_mulVec_alphaAllUpState K ν i)

/-- **`[N̂_↑, â†_{p,↑}] = â†_{p,↑}`** (charge `+1`): the `α` creation operator is a
linear combination of up creations, each of which raises `N̂_↑` by one. -/
theorem flatBandTotalUpNumber_commutator_ACreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    fermionTotalUpNumber (2 * K + 1) * flatBandACreation K ν p 0 =
      flatBandACreation K ν p 0 * fermionTotalUpNumber (2 * K + 1) +
        flatBandACreation K ν p 0 := by
  unfold flatBandACreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : fermionTotalUpNumber (2 * K + 1) *
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) =
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) *
        fermionTotalUpNumber (2 * K + 1) +
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) := by
    have h := fermionTotalUpNumber_commutator_fermionUpCreation (2 * K + 1) x
    unfold fermionUpCreation at h
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  rw [mul_smul_comm, smul_mul_assoc, hx, smul_add]

/-- **`N̂_↑ |Φα,all↑⟩ = (K + 1) |Φα,all↑⟩`.**  Each of the `K + 1` ordered
creations `â†_{p,↑}` raises the total up number by one (charge move-through over
the product). -/
theorem flatBandTotalUpNumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalUpNumber (2 * K + 1)).mulVec (flatBandAlphaAllUpState K ν) =
      ((K + 1 : ℕ) : ℂ) • flatBandAlphaAllUpState K ν := by
  unfold flatBandAlphaAllUpState
  rw [Matrix.mulVec_mulVec,
    charge_listProd_mulVec_vacuum (fermionTotalUpNumber (2 * K + 1))
      (fun p => flatBandACreation K ν p 0) (List.finRange (K + 1))
      (fermionTotalUpNumber_mulVec_vacuum (2 * K + 1))
      (fun p _ => flatBandTotalUpNumber_commutator_ACreation K ν p),
    List.length_finRange]

/-- **`Ŝ^z_tot |Φα,all↑⟩ = ((K + 1)/2) |Φα,all↑⟩`** (eq. (11.3.10)).  Since
`Ŝ^z_tot = (1/2)(N̂_↑ − N̂_↓)` and the all-up state has `N̂_↑ = K + 1`, `N̂_↓ = 0`,
the highest weight is `m = (K + 1)/2 = |E|/2` — the half-filled-band ferromagnetic
weight, strictly below the chain maximum `N/2 = (2K + 1)/2`. -/
theorem flatBandTotalSpinZ_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalSpinZ (2 * K + 1)).mulVec (flatBandAlphaAllUpState K ν) =
      (((K + 1 : ℕ) : ℂ) / 2) • flatBandAlphaAllUpState K ν := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    flatBandTotalUpNumber_mulVec_alphaAllUpState,
    flatBandTotalDownNumber_mulVec_alphaAllUpState, sub_zero, smul_smul]
  congr 1
  ring

end LatticeSystem.Fermion
