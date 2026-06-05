import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetry

/-!
# Total-`Ŝ⁺` invariance of the ferromagnetic t-J model (Tasaki §11.5)

`[Ĥ_tJ, Ŝ⁺_tot] = 0`: the t-J Hamiltonian commutes with the total spin-raising operator.  Together
with the total-`Ŝ³` conservation (`TJSpinSymmetry.lean`) and the lowering version (by Hermitian
adjoint), this gives the full SU(2) invariance used to discharge Proposition 11.24 (Issue #4230) via
the spin-½ sector reduction (Theorem A.17).

The site su(2) relations `[Ŝ⁺_tot, Ŝ^α_x]` are obtained from the existing single-operator
commutators of `Ŝ⁺_tot` with the fermion creation/annihilation operators
(`fermionUpAnnihilation_commutator_fermionTotalSpinPlus`, …), exactly the bilinear-product pattern
behind `fermionTotalSpinPlus_commute_hubbardKinetic`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, eq. (11.5.4), p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ### Site su(2) relations for `Ŝ⁺_tot` -/

/-- `Ŝ⁺_tot` commutes with each site raising operator `Ŝ⁺_x` (both `ĉ†_{x↑}` and `ĉ_{x↓}` commute
with `Ŝ⁺_tot`). -/
theorem totalSpinPlus_commute_siteSpinPlus (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N) (fermionSiteSpinPlus N x) := by
  unfold fermionSiteSpinPlus
  exact ((fermionUpCreation_commute_fermionTotalSpinPlus N x).symm).mul_right
    (fermionDownAnnihilation_commute_fermionTotalSpinPlus N x).symm

/-- `Ŝ⁺_tot Ŝ³_x = Ŝ³_x Ŝ⁺_tot − Ŝ⁺_x`, i.e. `[Ŝ⁺_tot, Ŝ³_x] = −Ŝ⁺_x`. -/
theorem totalSpinPlus_mul_siteSpinZ (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalSpinPlus N * fermionSiteSpinZ N x =
      fermionSiteSpinZ N x * fermionTotalSpinPlus N - fermionSiteSpinPlus N x := by
  have hcr_up := ((fermionUpCreation_commute_fermionTotalSpinPlus N x).symm).eq
  have hann_dn := ((fermionDownAnnihilation_commute_fermionTotalSpinPlus N x).symm).eq
  have hann_up : fermionTotalSpinPlus N * fermionUpAnnihilation N x =
      fermionUpAnnihilation N x * fermionTotalSpinPlus N - fermionDownAnnihilation N x := by
    have h := fermionUpAnnihilation_commutator_fermionTotalSpinPlus N x
    linear_combination (norm := noncomm_ring) -h
  have hcr_dn : fermionTotalSpinPlus N * fermionDownCreation N x =
      fermionDownCreation N x * fermionTotalSpinPlus N + fermionUpCreation N x := by
    have h := fermionDownCreation_commutator_fermionTotalSpinPlus N x
    linear_combination (norm := noncomm_ring) -h
  unfold fermionSiteSpinZ fermionSiteSpinPlus
  -- `Ŝ³_x = ½(ĉ†_{x↑}ĉ_{x↑} − ĉ†_{x↓}ĉ_{x↓})`; push `Ŝ⁺_tot` through each factor.
  have hup : fermionTotalSpinPlus N * (fermionUpCreation N x * fermionUpAnnihilation N x) =
      fermionUpCreation N x * fermionUpAnnihilation N x * fermionTotalSpinPlus N -
        fermionUpCreation N x * fermionDownAnnihilation N x := by
    calc fermionTotalSpinPlus N * (fermionUpCreation N x * fermionUpAnnihilation N x)
        = (fermionTotalSpinPlus N * fermionUpCreation N x) * fermionUpAnnihilation N x := by
          rw [← mul_assoc]
      _ = fermionUpCreation N x * (fermionTotalSpinPlus N * fermionUpAnnihilation N x) := by
          rw [hcr_up, mul_assoc]
      _ = fermionUpCreation N x *
            (fermionUpAnnihilation N x * fermionTotalSpinPlus N - fermionDownAnnihilation N x) := by
          rw [hann_up]
      _ = fermionUpCreation N x * fermionUpAnnihilation N x * fermionTotalSpinPlus N -
            fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring
  have hdn : fermionTotalSpinPlus N * (fermionDownCreation N x * fermionDownAnnihilation N x) =
      fermionDownCreation N x * fermionDownAnnihilation N x * fermionTotalSpinPlus N +
        fermionUpCreation N x * fermionDownAnnihilation N x := by
    calc fermionTotalSpinPlus N * (fermionDownCreation N x * fermionDownAnnihilation N x)
        = (fermionTotalSpinPlus N * fermionDownCreation N x) * fermionDownAnnihilation N x := by
          rw [← mul_assoc]
      _ = (fermionDownCreation N x * fermionTotalSpinPlus N + fermionUpCreation N x) *
            fermionDownAnnihilation N x := by rw [hcr_dn]
      _ = fermionDownCreation N x * (fermionTotalSpinPlus N * fermionDownAnnihilation N x) +
            fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring
      _ = fermionDownCreation N x * (fermionDownAnnihilation N x * fermionTotalSpinPlus N) +
            fermionUpCreation N x * fermionDownAnnihilation N x := by rw [hann_dn]
      _ = fermionDownCreation N x * fermionDownAnnihilation N x * fermionTotalSpinPlus N +
            fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring
  rw [Matrix.mul_smul, mul_sub, hup, hdn, Matrix.smul_mul, sub_mul]
  module

/-- The su(2) relation `Ŝ⁺_tot Ŝ⁻_x = Ŝ⁻_x Ŝ⁺_tot + 2 Ŝ³_x`, i.e. `[Ŝ⁺_tot, Ŝ⁻_x] = 2 Ŝ³_x`. -/
theorem totalSpinPlus_mul_siteSpinMinus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalSpinPlus N * fermionSiteSpinMinus N x =
      fermionSiteSpinMinus N x * fermionTotalSpinPlus N +
        (2 : ℂ) • fermionSiteSpinZ N x := by
  have hann_up : fermionTotalSpinPlus N * fermionUpAnnihilation N x =
      fermionUpAnnihilation N x * fermionTotalSpinPlus N - fermionDownAnnihilation N x := by
    have h := fermionUpAnnihilation_commutator_fermionTotalSpinPlus N x
    linear_combination (norm := noncomm_ring) -h
  have hcr_dn : fermionTotalSpinPlus N * fermionDownCreation N x =
      fermionDownCreation N x * fermionTotalSpinPlus N + fermionUpCreation N x := by
    have h := fermionDownCreation_commutator_fermionTotalSpinPlus N x
    linear_combination (norm := noncomm_ring) -h
  unfold fermionSiteSpinMinus fermionSiteSpinZ
  rw [show fermionTotalSpinPlus N * (fermionDownCreation N x * fermionUpAnnihilation N x)
        = (fermionTotalSpinPlus N * fermionDownCreation N x) * fermionUpAnnihilation N x from by
      rw [← mul_assoc], hcr_dn, add_mul, mul_assoc, hann_up]
  -- `(ĉ†↓ Ŝ⁺ + ĉ†↑) ĉ↑` expanded; collect using `ĉ†↑ĉ↑ − ĉ†↓ĉ↓ = 2 Ŝ³` after the swap.
  rw [show fermionDownCreation N x *
        (fermionUpAnnihilation N x * fermionTotalSpinPlus N - fermionDownAnnihilation N x) +
        fermionUpCreation N x * fermionUpAnnihilation N x
      = fermionDownCreation N x * fermionUpAnnihilation N x * fermionTotalSpinPlus N +
        (fermionUpCreation N x * fermionUpAnnihilation N x -
          fermionDownCreation N x * fermionDownAnnihilation N x) from by noncomm_ring]
  module

/-! ### Commutation with the interaction and kinetic terms -/

/-- `Ŝ⁺_tot` commutes with the two-site spin dot product `Ŝ_x · Ŝ_y` (SU(2) scalar). -/
theorem totalSpinPlus_commute_fermionSpinDot (N : ℕ) (x y : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N) (fermionSpinDot N x y) := by
  set S := fermionTotalSpinPlus N
  have hR1x := (totalSpinPlus_commute_siteSpinPlus N x).eq
  have hR1y := (totalSpinPlus_commute_siteSpinPlus N y).eq
  have hR2x := totalSpinPlus_mul_siteSpinZ N x
  have hR2y := totalSpinPlus_mul_siteSpinZ N y
  have hR3x := totalSpinPlus_mul_siteSpinMinus N x
  have hR3y := totalSpinPlus_mul_siteSpinMinus N y
  -- `S (Ŝ⁺_x Ŝ⁻_y) = Ŝ⁺_x Ŝ⁻_y S + 2 Ŝ⁺_x Ŝ³_y`.
  have hA : S * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y) =
      fermionSiteSpinPlus N x * fermionSiteSpinMinus N y * S +
        (2 : ℂ) • (fermionSiteSpinPlus N x * fermionSiteSpinZ N y) := by
    rw [show S * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
          = (S * fermionSiteSpinPlus N x) * fermionSiteSpinMinus N y from by rw [← mul_assoc],
      hR1x, mul_assoc, hR3y, mul_add, ← mul_assoc, Matrix.mul_smul]
  -- `S (Ŝ⁻_x Ŝ⁺_y) = Ŝ⁻_x Ŝ⁺_y S + 2 Ŝ³_x Ŝ⁺_y`.
  have hB : S * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y) =
      fermionSiteSpinMinus N x * fermionSiteSpinPlus N y * S +
        (2 : ℂ) • (fermionSiteSpinZ N x * fermionSiteSpinPlus N y) := by
    rw [show S * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)
          = (S * fermionSiteSpinMinus N x) * fermionSiteSpinPlus N y from by rw [← mul_assoc],
      hR3x, add_mul, mul_assoc, hR1y, ← mul_assoc, smul_mul_assoc]
  -- `S (Ŝ³_x Ŝ³_y) = Ŝ³_x Ŝ³_y S − Ŝ⁺_x Ŝ³_y − Ŝ³_x Ŝ⁺_y`.
  have hC : S * (fermionSiteSpinZ N x * fermionSiteSpinZ N y) =
      fermionSiteSpinZ N x * fermionSiteSpinZ N y * S -
        fermionSiteSpinPlus N x * fermionSiteSpinZ N y -
        fermionSiteSpinZ N x * fermionSiteSpinPlus N y := by
    rw [show S * (fermionSiteSpinZ N x * fermionSiteSpinZ N y)
          = (S * fermionSiteSpinZ N x) * fermionSiteSpinZ N y from by rw [← mul_assoc],
      hR2x, sub_mul, mul_assoc, hR2y, mul_sub]
    noncomm_ring
  have key : S * fermionSpinDot N x y = fermionSpinDot N x y * S := by
    unfold fermionSpinDot
    rw [mul_add, Matrix.mul_smul, mul_add, hA, hB, hC, add_mul, smul_mul_assoc, add_mul]
    module
  exact key

/-- `Ŝ⁺_tot` commutes with the per-site total number `n̂_x` (number conservation). -/
theorem totalSpinPlus_commute_fermionSiteNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N) (fermionSiteNumber N x) := by
  set S := fermionTotalSpinPlus N
  have hcr_up := ((fermionUpCreation_commute_fermionTotalSpinPlus N x).symm).eq
  have hann_dn := ((fermionDownAnnihilation_commute_fermionTotalSpinPlus N x).symm).eq
  have hann_up : S * fermionUpAnnihilation N x =
      fermionUpAnnihilation N x * S - fermionDownAnnihilation N x := by
    have h := fermionUpAnnihilation_commutator_fermionTotalSpinPlus N x
    linear_combination (norm := noncomm_ring) -h
  have hcr_dn : S * fermionDownCreation N x =
      fermionDownCreation N x * S + fermionUpCreation N x := by
    have h := fermionDownCreation_commutator_fermionTotalSpinPlus N x
    linear_combination (norm := noncomm_ring) -h
  have key : S * fermionSiteNumber N x = fermionSiteNumber N x * S := by
    unfold fermionSiteNumber fermionUpNumber fermionDownNumber
    rw [show fermionMultiNumber (2 * N + 1) (spinfulIndex N x 0) =
        fermionUpCreation N x * fermionUpAnnihilation N x from rfl,
      show fermionMultiNumber (2 * N + 1) (spinfulIndex N x 1) =
        fermionDownCreation N x * fermionDownAnnihilation N x from rfl]
    rw [mul_add, add_mul,
      show S * (fermionUpCreation N x * fermionUpAnnihilation N x)
        = (S * fermionUpCreation N x) * fermionUpAnnihilation N x from by rw [← mul_assoc],
      hcr_up, mul_assoc, hann_up,
      show S * (fermionDownCreation N x * fermionDownAnnihilation N x)
        = (S * fermionDownCreation N x) * fermionDownAnnihilation N x from by rw [← mul_assoc],
      hcr_dn, add_mul, mul_assoc, hann_dn]
    noncomm_ring
  exact key

/-- `Ŝ⁺_tot` commutes with the hard-core projected hopping `P̂hc K̂ P̂hc`. -/
theorem totalSpinPlus_commute_tJKinetic (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] :
    Commute (fermionTotalSpinPlus N)
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
        hubbardHardcoreProjection N) := by
  have hP := fermionTotalSpinPlus_commute_hubbardHardcoreProjection N
  have hK : Commute (fermionTotalSpinPlus N) (hubbardKineticOnGraph N G 1) := by
    unfold hubbardKineticOnGraph
    exact fermionTotalSpinPlus_commute_hubbardKinetic N _
  exact (hP.mul_right hK).mul_right hP

/-- **Total-`Ŝ⁺` invariance of the ferromagnetic t-J model:** `[Ĥ_tJ, Ŝ⁺_tot] = 0`. -/
theorem fermionTotalSpinPlus_commute_tJHamiltonian (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    Commute (fermionTotalSpinPlus N) (tJHamiltonian N G τ J) := by
  unfold tJHamiltonian
  refine (Commute.smul_right ?_ _).add_right (Commute.smul_right ?_ _)
  · exact totalSpinPlus_commute_tJKinetic N G
  · refine Commute.sum_right _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => ?_))
    by_cases h : G.Adj x y
    · simp only [h, if_true]
      exact ((Commute.smul_right
        ((totalSpinPlus_commute_fermionSiteNumber N x).mul_right
          (totalSpinPlus_commute_fermionSiteNumber N y)) _).sub_right
        (totalSpinPlus_commute_fermionSpinDot N x y))
    · simp only [h, if_false, Commute.zero_right]

end LatticeSystem.Fermion
