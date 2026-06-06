import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetry

/-!
# Tasaki 11.5: the t-J Hamiltonian conserves particle number (Prop 11.24 PR-E1b commute-N)

`[Ĥ_tJ, N̂] = 0`: the ferromagnetic t-J Hamiltonian commutes with the total electron number.
This is the charge half of the conservation laws (the spin half `[Ĥ_tJ, Ŝ^α] = 0` is established),
and it is needed for the operator-lift sector closure: `Ĥ_tJ |Φ_s⟩` stays in the `N̂ = Ne` sector.

The proof mirrors `fermionTotalSpinZ_commute_tJHamiltonian`: each piece of `Ĥ_tJ` commutes with
`N̂` — the kinetic sandwich (hard-core projection and hopping both conserve number), the density
products `n̂_x n̂_y` (diagonal), and the per-site spin dot `Ŝ_x · Ŝ_y` (its ladders are
number-conserving hops, its `Ŝ³`-product is diagonal).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443 (and §9.3.3 for the U(1) charge symmetry).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-- `Ŝ⁺_x = ĉ†_{x↑}ĉ_{x↓}` is a number-conserving hop, so it commutes with `N̂`. -/
theorem fermionTotalNumber_commute_fermionSiteSpinPlus (x : Fin (N + 1)) :
    Commute (fermionTotalNumber (2 * N + 1)) (fermionSiteSpinPlus N x) := by
  unfold fermionSiteSpinPlus fermionUpCreation fermionDownAnnihilation
  exact fermionTotalNumber_commute_hopping (2 * N + 1) (spinfulIndex N x 0) (spinfulIndex N x 1)

/-- `Ŝ⁻_x = ĉ†_{x↓}ĉ_{x↑}` is a number-conserving hop, so it commutes with `N̂`. -/
theorem fermionTotalNumber_commute_fermionSiteSpinMinus (x : Fin (N + 1)) :
    Commute (fermionTotalNumber (2 * N + 1)) (fermionSiteSpinMinus N x) := by
  unfold fermionSiteSpinMinus fermionDownCreation fermionUpAnnihilation
  exact fermionTotalNumber_commute_hopping (2 * N + 1) (spinfulIndex N x 1) (spinfulIndex N x 0)

/-- `Ŝ³_x` is diagonal in the occupation basis, so it commutes with `N̂`. -/
theorem fermionTotalNumber_commute_fermionSiteSpinZ (x : Fin (N + 1)) :
    Commute (fermionTotalNumber (2 * N + 1)) (fermionSiteSpinZ N x) := by
  unfold fermionSiteSpinZ fermionUpCreation fermionUpAnnihilation fermionDownCreation
    fermionDownAnnihilation
  refine Commute.smul_right (Commute.sub_right ?_ ?_) _
  · exact (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N x 0)).symm
  · exact (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N x 1)).symm

/-- The site number `n̂_x = n̂_{x↑} + n̂_{x↓}` commutes with `N̂` (diagonal). -/
theorem fermionTotalNumber_commute_fermionSiteNumber (x : Fin (N + 1)) :
    Commute (fermionTotalNumber (2 * N + 1)) (fermionSiteNumber N x) := by
  unfold fermionSiteNumber fermionUpNumber fermionDownNumber
  exact Commute.add_right
    (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N x 0)).symm
    (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N x 1)).symm

/-- The per-site spin dot `Ŝ_x · Ŝ_y` commutes with `N̂` (ladders are number-conserving hops; the
`Ŝ³`-product is diagonal). -/
theorem fermionTotalNumber_commute_fermionSpinDot (x y : Fin (N + 1)) :
    Commute (fermionTotalNumber (2 * N + 1)) (fermionSpinDot N x y) := by
  unfold fermionSpinDot
  refine Commute.add_right (Commute.smul_right (Commute.add_right ?_ ?_) _) ?_
  · exact (fermionTotalNumber_commute_fermionSiteSpinPlus x).mul_right
      (fermionTotalNumber_commute_fermionSiteSpinMinus y)
  · exact (fermionTotalNumber_commute_fermionSiteSpinMinus x).mul_right
      (fermionTotalNumber_commute_fermionSiteSpinPlus y)
  · exact (fermionTotalNumber_commute_fermionSiteSpinZ x).mul_right
      (fermionTotalNumber_commute_fermionSiteSpinZ y)

/-- The t-J kinetic sandwich `P̂hc K P̂hc` commutes with `N̂` (projection and hopping both conserve
number). -/
theorem fermionTotalNumber_commute_tJKinetic (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] :
    Commute (fermionTotalNumber (2 * N + 1))
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
        hubbardHardcoreProjection N) := by
  refine ((hubbardHardcoreProjection_commute_fermionTotalNumber N).symm.mul_right ?_).mul_right
    (hubbardHardcoreProjection_commute_fermionTotalNumber N).symm
  exact (hubbardKineticOnGraph_commute_fermionTotalNumber N G 1).symm

/-- **`[Ĥ_tJ, N̂] = 0`: the t-J Hamiltonian conserves total particle number.** -/
theorem fermionTotalNumber_commute_tJHamiltonian (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    Commute (fermionTotalNumber (2 * N + 1)) (tJHamiltonian N G τ J) := by
  unfold tJHamiltonian
  refine (Commute.smul_right ?_ _).add_right (Commute.smul_right ?_ _)
  · exact fermionTotalNumber_commute_tJKinetic G
  · refine Commute.sum_right _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => ?_))
    by_cases h : G.Adj x y
    · simp only [h, if_true]
      exact (Commute.smul_right
        ((fermionTotalNumber_commute_fermionSiteNumber x).mul_right
          (fermionTotalNumber_commute_fermionSiteNumber y)) _).sub_right
        (fermionTotalNumber_commute_fermionSpinDot x y)
    · simp only [h, if_false, Commute.zero_right]

end LatticeSystem.Fermion
