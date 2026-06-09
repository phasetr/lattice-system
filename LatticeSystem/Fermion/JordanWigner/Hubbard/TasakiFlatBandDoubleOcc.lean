import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandFrustrationFree
import LatticeSystem.Fermion.JordanWigner.CAR.SameSite
import LatticeSystem.Math.RayleighPosSemidefKernel

/-!
# Tasaki §11.3.1: the double annihilation kills a ground state (toward block ≤ 1)

The on-site double occupancy is `n̂_{x↑} n̂_{x↓} = (ĉ_{x↓} ĉ_{x↑})ᴴ (ĉ_{x↓} ĉ_{x↑})` (rearrange the
two number operators by the cross-spin CAR `{ĉ_{x↑}, ĉ†_{x↓}} = 0`, `{ĉ_{x↑}, ĉ_{x↓}} = 0`).  A
ground state has `n̂_{x↑} n̂_{x↓} v = 0` (no double occupancy, eq. (11.3.12)), so the positive-
semidefinite kernel argument forces the double annihilation itself to vanish: `ĉ_{x↓} ĉ_{x↑} v = 0`.
This operator form (not the diagonal one) is what the site-annihilation peel consumes.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eq. (11.3.12).  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {K : ℕ} {ν : ℝ}

/-- The down-then-up site annihilation `ĉ_{x↓} ĉ_{x↑}` at the physical site `x`. -/
noncomputable def cDownUp (K : ℕ) (x : Fin (2 * K + 2)) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1) *
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0)

/-- **`n̂_{x↑} n̂_{x↓} = (ĉ_{x↓} ĉ_{x↑})ᴴ (ĉ_{x↓} ĉ_{x↑})`.**  Moving the inner `ĉ_{x↑} ĉ†_{x↓}` and
`ĉ_{x↑} ĉ_{x↓}` past each other by the cross-spin anticommutators recasts the diagonal double
occupancy as the Gram operator of the double annihilation. -/
theorem hubbardDoubleOccupancy_eq_conjTranspose_mul_self (K : ℕ) (x : Fin (2 * K + 2)) :
    hubbardDoubleOccupancy (2 * K + 1) x = (cDownUp K x)ᴴ * cDownUp K x := by
  rw [hubbardDoubleOccupancy, fermionUpNumber, fermionDownNumber, fermionMultiNumber,
    fermionMultiNumber, cDownUp, Matrix.conjTranspose_mul, fermionMultiAnnihilation_conjTranspose,
    fermionMultiAnnihilation_conjTranspose]
  set cup := fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0)
  set cdn := fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1)
  set cre := fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1)
  have hcd : cup * cre = -(cre * cup) := by
    have h := spinful_annihilation_creation_anticomm K x x 0 1
    rw [if_neg (fun hc => absurd hc.2 (by decide))] at h
    exact eq_neg_of_add_eq_zero_left h
  have haa : cup * cdn = -(cdn * cup) :=
    eq_neg_of_add_eq_zero_left
      (fermionMultiAnnihilation_anticomm_of_ne (spinfulIndex_up_ne_down (2 * K + 1) x x))
  have hmid : cup * (cre * cdn) = cre * (cdn * cup) := by
    rw [← mul_assoc, hcd, neg_mul, mul_assoc, haa, mul_neg]
    exact neg_neg _
  simp only [mul_assoc]
  rw [hmid]

/-- **`ĉ_{x↓} ĉ_{x↑} v = 0`** for any flat-band ground state `v` (the operator form of the
no-double-occupancy condition): from `n̂_{x↑} n̂_{x↓} v = 0` and the Gram identity, by the PSD
kernel. -/
theorem flatBand_groundState_doubleAnnihilation_mulVec_eq_zero (K : ℕ) (ν t U : ℝ)
    (ht : 0 ≤ t) (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0) (x : Fin (2 * K + 2)) :
    (cDownUp K x).mulVec v = 0 := by
  have hdo := flatBand_groundState_doubleOccupancy_mulVec_eq_zero K ν t U ht hU hv x
  rw [hubbardDoubleOccupancy_eq_conjTranspose_mul_self] at hdo
  exact conjTranspose_mul_self_mulVec_eq_zero hdo

end LatticeSystem.Fermion
