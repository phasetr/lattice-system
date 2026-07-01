import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel

/-!
# Total-`Ŝ³` conservation of the ferromagnetic t-J model (Tasaki §11.5)

`[Ĥ_tJ, Ŝ³_tot] = 0`: the t-J Hamiltonian conserves the total `z`-magnetization.  This is the
abelian (`U(1)`) part of the SU(2) invariance used in the discharge of Proposition 11.24 (Issue
#4230); it underlies the magnetization-sector decomposition of the ground subspace.

The kinetic (hard-core projected hopping) part reuses the existing total-number / hard-core
projection commutations.  The new ingredient is the exchange term: `Ŝ³_tot` commutes with the
per-bond `n̂_x n̂_y / 4 − Ŝ_x · Ŝ_y`, via the site weight relations `[Ŝ³_tot, Ŝ^±_x] = ±Ŝ^±_x`
derived from the total-number / creation-annihilation commutators.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, eq. (11.5.4), p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- Weight relation `N̂_↑ Ŝ^+_x = Ŝ^+_x (N̂_↑ + 1)`: the up-number raises by one on `Ŝ^+_x`. -/
private theorem totalUpNumber_mul_siteSpinPlus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalUpNumber N * fermionSiteSpinPlus N x =
      fermionSiteSpinPlus N x * fermionTotalUpNumber N + fermionSiteSpinPlus N x := by
  unfold fermionSiteSpinPlus
  have hcr : fermionTotalUpNumber N * fermionUpCreation N x =
      fermionUpCreation N x * fermionTotalUpNumber N + fermionUpCreation N x := by
    have h := fermionTotalUpNumber_commutator_fermionUpCreation N x
    linear_combination (norm := noncomm_ring) h
  have hdn := (fermionTotalUpNumber_commute_fermionDownAnnihilation N x).eq
  calc fermionTotalUpNumber N * (fermionUpCreation N x * fermionDownAnnihilation N x)
      = (fermionTotalUpNumber N * fermionUpCreation N x) * fermionDownAnnihilation N x := by
        rw [← mul_assoc]
    _ = (fermionUpCreation N x * fermionTotalUpNumber N + fermionUpCreation N x) *
          fermionDownAnnihilation N x := by rw [hcr]
    _ = fermionUpCreation N x * (fermionTotalUpNumber N * fermionDownAnnihilation N x) +
          fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring
    _ = fermionUpCreation N x * (fermionDownAnnihilation N x * fermionTotalUpNumber N) +
          fermionUpCreation N x * fermionDownAnnihilation N x := by rw [hdn]
    _ = fermionUpCreation N x * fermionDownAnnihilation N x * fermionTotalUpNumber N +
          fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring

/-- Weight relation `N̂_↓ Ŝ^+_x = Ŝ^+_x (N̂_↓ − 1)`: the down-number lowers by one on `Ŝ^+_x`. -/
theorem totalDownNumber_mul_siteSpinPlus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionSiteSpinPlus N x =
      fermionSiteSpinPlus N x * fermionTotalDownNumber N - fermionSiteSpinPlus N x := by
  unfold fermionSiteSpinPlus
  have hup := (fermionTotalDownNumber_commute_fermionUpCreation N x).eq
  have han : fermionTotalDownNumber N * fermionDownAnnihilation N x =
      fermionDownAnnihilation N x * fermionTotalDownNumber N - fermionDownAnnihilation N x := by
    have h := fermionTotalDownNumber_commutator_fermionDownAnnihilation N x
    linear_combination (norm := noncomm_ring) h
  calc fermionTotalDownNumber N * (fermionUpCreation N x * fermionDownAnnihilation N x)
      = (fermionTotalDownNumber N * fermionUpCreation N x) * fermionDownAnnihilation N x := by
        rw [← mul_assoc]
    _ = (fermionUpCreation N x * fermionTotalDownNumber N) * fermionDownAnnihilation N x := by
        rw [hup]
    _ = fermionUpCreation N x * (fermionTotalDownNumber N * fermionDownAnnihilation N x) := by
        rw [mul_assoc]
    _ = fermionUpCreation N x *
          (fermionDownAnnihilation N x * fermionTotalDownNumber N -
            fermionDownAnnihilation N x) := by
        rw [han]
    _ = fermionUpCreation N x * fermionDownAnnihilation N x * fermionTotalDownNumber N -
          fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring

/-- `Ŝ³_tot Ŝ^+_x = Ŝ^+_x Ŝ³_tot + Ŝ^+_x`, i.e. `[Ŝ³_tot, Ŝ^+_x] = Ŝ^+_x`. -/
theorem totalSpinZ_mul_siteSpinPlus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalSpinZ N * fermionSiteSpinPlus N x =
      fermionSiteSpinPlus N x * fermionTotalSpinZ N + fermionSiteSpinPlus N x := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mul, sub_mul, totalUpNumber_mul_siteSpinPlus, totalDownNumber_mul_siteSpinPlus,
    Matrix.mul_smul, mul_sub]
  module

/-- Weight relation `N̂_↑ Ŝ^-_x = Ŝ^-_x (N̂_↑ − 1)`: `Ŝ^-_x` annihilates one up-spin. -/
private theorem totalUpNumber_mul_siteSpinMinus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalUpNumber N * fermionSiteSpinMinus N x =
      fermionSiteSpinMinus N x * fermionTotalUpNumber N - fermionSiteSpinMinus N x := by
  unfold fermionSiteSpinMinus
  have hdc := (fermionTotalUpNumber_commute_fermionDownCreation N x).eq
  have han : fermionTotalUpNumber N * fermionUpAnnihilation N x =
      fermionUpAnnihilation N x * fermionTotalUpNumber N - fermionUpAnnihilation N x := by
    have h := fermionTotalUpNumber_commutator_fermionUpAnnihilation N x
    linear_combination (norm := noncomm_ring) h
  calc fermionTotalUpNumber N * (fermionDownCreation N x * fermionUpAnnihilation N x)
      = (fermionTotalUpNumber N * fermionDownCreation N x) * fermionUpAnnihilation N x := by
        rw [← mul_assoc]
    _ = (fermionDownCreation N x * fermionTotalUpNumber N) * fermionUpAnnihilation N x := by
        rw [hdc]
    _ = fermionDownCreation N x * (fermionTotalUpNumber N * fermionUpAnnihilation N x) := by
        rw [mul_assoc]
    _ = fermionDownCreation N x *
          (fermionUpAnnihilation N x * fermionTotalUpNumber N - fermionUpAnnihilation N x) := by
        rw [han]
    _ = fermionDownCreation N x * fermionUpAnnihilation N x * fermionTotalUpNumber N -
          fermionDownCreation N x * fermionUpAnnihilation N x := by noncomm_ring

/-- Weight relation `N̂_↓ Ŝ^-_x = Ŝ^-_x (N̂_↓ + 1)`: `Ŝ^-_x` creates one down-spin. -/
private theorem totalDownNumber_mul_siteSpinMinus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionSiteSpinMinus N x =
      fermionSiteSpinMinus N x * fermionTotalDownNumber N + fermionSiteSpinMinus N x := by
  unfold fermionSiteSpinMinus
  have hcr : fermionTotalDownNumber N * fermionDownCreation N x =
      fermionDownCreation N x * fermionTotalDownNumber N + fermionDownCreation N x := by
    have h := fermionTotalDownNumber_commutator_fermionDownCreation N x
    linear_combination (norm := noncomm_ring) h
  have hua := (fermionTotalDownNumber_commute_fermionUpAnnihilation N x).eq
  calc fermionTotalDownNumber N * (fermionDownCreation N x * fermionUpAnnihilation N x)
      = (fermionTotalDownNumber N * fermionDownCreation N x) * fermionUpAnnihilation N x := by
        rw [← mul_assoc]
    _ = (fermionDownCreation N x * fermionTotalDownNumber N + fermionDownCreation N x) *
          fermionUpAnnihilation N x := by rw [hcr]
    _ = fermionDownCreation N x * (fermionTotalDownNumber N * fermionUpAnnihilation N x) +
          fermionDownCreation N x * fermionUpAnnihilation N x := by noncomm_ring
    _ = fermionDownCreation N x * (fermionUpAnnihilation N x * fermionTotalDownNumber N) +
          fermionDownCreation N x * fermionUpAnnihilation N x := by rw [hua]
    _ = fermionDownCreation N x * fermionUpAnnihilation N x * fermionTotalDownNumber N +
          fermionDownCreation N x * fermionUpAnnihilation N x := by noncomm_ring

/-- `Ŝ³_tot Ŝ^-_x = Ŝ^-_x Ŝ³_tot − Ŝ^-_x`, i.e. `[Ŝ³_tot, Ŝ^-_x] = −Ŝ^-_x`. -/
theorem totalSpinZ_mul_siteSpinMinus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalSpinZ N * fermionSiteSpinMinus N x =
      fermionSiteSpinMinus N x * fermionTotalSpinZ N - fermionSiteSpinMinus N x := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mul, sub_mul, totalUpNumber_mul_siteSpinMinus, totalDownNumber_mul_siteSpinMinus,
    Matrix.mul_smul, mul_sub]
  module

/-- From the weight relations `A B = B A + B` and `A C = C A − C`, the product `B C` commutes
with `A` (total weight `0`). -/
private theorem commute_of_weight_pos_neg {A B C : ManyBodyOp (Fin (2 * N + 2))}
    (hB : A * B = B * A + B) (hC : A * C = C * A - C) : Commute A (B * C) := by
  have h : A * (B * C) = (B * C) * A :=
    calc A * (B * C) = (A * B) * C := by rw [← mul_assoc]
      _ = (B * A + B) * C := by rw [hB]
      _ = B * (A * C) + B * C := by noncomm_ring
      _ = B * (C * A - C) + B * C := by rw [hC]
      _ = B * C * A := by noncomm_ring
  exact h

/-- Mirror of `commute_of_weight_pos_neg` with the weights reversed (`A B = B A − B`,
`A C = C A + C`). -/
private theorem commute_of_weight_neg_pos {A B C : ManyBodyOp (Fin (2 * N + 2))}
    (hB : A * B = B * A - B) (hC : A * C = C * A + C) : Commute A (B * C) := by
  have h : A * (B * C) = (B * C) * A :=
    calc A * (B * C) = (A * B) * C := by rw [← mul_assoc]
      _ = (B * A - B) * C := by rw [hB]
      _ = B * (A * C) - B * C := by noncomm_ring
      _ = B * (C * A + C) - B * C := by rw [hC]
      _ = B * C * A := by noncomm_ring
  exact h

/-- `Ŝ³_tot = ½(N̂_↑ − N̂_↓)` commutes with any operator that commutes with both total numbers. -/
private theorem totalSpinZ_commute_of_up_down {X : ManyBodyOp (Fin (2 * N + 2))}
    (hup : Commute (fermionTotalUpNumber N) X) (hdown : Commute (fermionTotalDownNumber N) X) :
    Commute (fermionTotalSpinZ N) X := by
  unfold fermionTotalSpinZ
  exact (hup.sub_left hdown).smul_left _

/-- `N̂_↑` commutes with each site up-number (all number operators commute). -/
private theorem totalUpNumber_commute_fermionUpNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionUpNumber N x) := by
  unfold fermionTotalUpNumber
  exact Commute.sum_left _ _ _ (fun k _ =>
    fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N k 0) (spinfulIndex N x 0))

/-- `N̂_↓` commutes with each site down-number. -/
private theorem totalDownNumber_commute_fermionDownNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionDownNumber N x) := by
  unfold fermionTotalDownNumber
  exact Commute.sum_left _ _ _ (fun k _ =>
    fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N k 1) (spinfulIndex N x 1))

/-- `Ŝ³_tot` commutes with each site up-number. -/
theorem totalSpinZ_commute_fermionUpNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (fermionUpNumber N x) :=
  totalSpinZ_commute_of_up_down (totalUpNumber_commute_fermionUpNumber N x)
    (fermionTotalDownNumber_commute_fermionUpNumber N x)

/-- `Ŝ³_tot` commutes with each site down-number. -/
theorem totalSpinZ_commute_fermionDownNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (fermionDownNumber N x) :=
  totalSpinZ_commute_of_up_down (fermionTotalUpNumber_commute_fermionDownNumber N x)
    (totalDownNumber_commute_fermionDownNumber N x)

/-- `Ŝ³_tot` commutes with each site `Ŝ³_x` (number-diagonal). -/
theorem totalSpinZ_commute_fermionSiteSpinZ (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (fermionSiteSpinZ N x) := by
  unfold fermionSiteSpinZ
  exact ((totalSpinZ_commute_fermionUpNumber N x).sub_right
    (totalSpinZ_commute_fermionDownNumber N x)).smul_right _

/-- `Ŝ³_tot` commutes with the per-site total number `n̂_x = n̂_{x↑} + n̂_{x↓}`. -/
theorem totalSpinZ_commute_fermionSiteNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (fermionSiteNumber N x) := by
  unfold fermionSiteNumber
  exact (totalSpinZ_commute_fermionUpNumber N x).add_right
    (totalSpinZ_commute_fermionDownNumber N x)

/-- `Ŝ³_tot` commutes with the two-site spin dot product `Ŝ_x · Ŝ_y` (SU(2) scalar, weight 0). -/
theorem totalSpinZ_commute_fermionSpinDot (N : ℕ) (x y : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (fermionSpinDot N x y) := by
  unfold fermionSpinDot
  have hpm : Commute (fermionTotalSpinZ N)
      (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y) :=
    commute_of_weight_pos_neg (totalSpinZ_mul_siteSpinPlus N x) (totalSpinZ_mul_siteSpinMinus N y)
  have hmp : Commute (fermionTotalSpinZ N)
      (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y) :=
    commute_of_weight_neg_pos (totalSpinZ_mul_siteSpinMinus N x) (totalSpinZ_mul_siteSpinPlus N y)
  have hzz : Commute (fermionTotalSpinZ N)
      (fermionSiteSpinZ N x * fermionSiteSpinZ N y) :=
    (totalSpinZ_commute_fermionSiteSpinZ N x).mul_right (totalSpinZ_commute_fermionSiteSpinZ N y)
  exact ((hpm.add_right hmp).smul_right _).add_right hzz

/-- `Ŝ³_tot` commutes with the hard-core projected hopping `P̂hc K̂ P̂hc`. -/
theorem totalSpinZ_commute_tJKinetic (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] :
    Commute (fermionTotalSpinZ N)
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
        hubbardHardcoreProjection N) := by
  have hP := fermionTotalSpinZ_commute_hubbardHardcoreProjection N
  have hK : Commute (fermionTotalSpinZ N) (hubbardKineticOnGraph N G 1) := by
    unfold hubbardKineticOnGraph
    exact totalSpinZ_commute_of_up_down
      (fermionTotalUpNumber_commute_hubbardKinetic N _)
      (fermionTotalDownNumber_commute_hubbardKinetic N _)
  exact (hP.mul_right hK).mul_right hP

/-- **Total-`Ŝ³` conservation of the ferromagnetic t-J model:** `[Ĥ_tJ, Ŝ³_tot] = 0`. -/
theorem fermionTotalSpinZ_commute_tJHamiltonian (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    Commute (fermionTotalSpinZ N) (tJHamiltonian N G τ J) := by
  unfold tJHamiltonian
  refine (Commute.smul_right ?_ _).add_right (Commute.smul_right ?_ _)
  · exact totalSpinZ_commute_tJKinetic N G
  · refine Commute.sum_right _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => ?_))
    by_cases h : G.Adj x y
    · simp only [h, if_true]
      exact ((Commute.smul_right
        ((totalSpinZ_commute_fermionSiteNumber N x).mul_right
          (totalSpinZ_commute_fermionSiteNumber N y)) _).sub_right
        (totalSpinZ_commute_fermionSpinDot N x y))
    · simp only [h, if_false, Commute.zero_right]

end LatticeSystem.Fermion
