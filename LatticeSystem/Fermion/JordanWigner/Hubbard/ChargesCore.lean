import LatticeSystem.Fermion.JordanWigner.Hubbard

/-!
# Hubbard spinful conserved charges and vacuum eigenstates (foundation)

Foundational layer extracted from `Charges.lean` for build speed.  This file defines the
spinful conserved charges `N_↑`, `N_↓`, `S^z_tot` and proves their commutation with the
Hubbard kinetic and on-site-interaction terms, together with the spinful vacuum
eigenstate corollaries.

The cross-spin commutativity (different species commute) is kept in the capstone module
`Charges.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Spinful conserved charges N_↑, N_↓, and S^z_tot

The spinful Hilbert space carries two natural U(1) charges
(particle numbers per spin) and one diagonal SU(2) charge
(z-component of total spin). They all commute pairwise (and with
the total particle number `N̂`); commute with the full Hubbard
Hamiltonian is deferred to a later PR. -/

/-- Total spin-up particle number `N_↑ = Σ_i n_{i,↑}`. -/
noncomputable def fermionTotalUpNumber (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionUpNumber N i

/-- Total spin-down particle number `N_↓ = Σ_i n_{i,↓}`. -/
noncomputable def fermionTotalDownNumber (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionDownNumber N i

/-- Total z-component of spin `S^z_tot = (1/2)(N_↑ − N_↓)`. -/
noncomputable def fermionTotalSpinZ (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) • (fermionTotalUpNumber N - fermionTotalDownNumber N)

/-- `N_↑` and `N_↓` commute (sums of pairwise commuting number
operators). -/
theorem fermionTotalUpNumber_commute_fermionTotalDownNumber (N : ℕ) :
    Commute (fermionTotalUpNumber N) (fermionTotalDownNumber N) := by
  unfold fermionTotalUpNumber fermionTotalDownNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_right _ _ _ (fun j _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 1)

/-- `N_↑` commutes with the total particle number `N̂` on the
underlying chain. -/
theorem fermionTotalUpNumber_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalUpNumber N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalUpNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0)

/-- `N_↓` commutes with the total particle number `N̂` on the
underlying chain. -/
theorem fermionTotalDownNumber_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalDownNumber N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalDownNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 1)

/-- The total z-spin `S^z_tot` commutes with the total particle
number `N̂`: free corollary of the up/down individual commutes. -/
theorem fermionTotalSpinZ_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinZ N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinZ
  refine Commute.smul_left ?_ _
  exact (fermionTotalUpNumber_commute_fermionTotalNumber N).sub_left
    (fermionTotalDownNumber_commute_fermionTotalNumber N)

/-- `N_↑` commutes with the Hubbard on-site interaction
`U Σ_i n_{i↑} n_{i↓}`. All summands are products of pairwise
commuting number operators. -/
theorem fermionTotalUpNumber_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalUpNumber hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ U
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the Hubbard on-site interaction. -/
theorem fermionTotalDownNumber_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalDownNumber hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ U
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 1)

/-- `S^z_tot` commutes with the Hubbard on-site interaction. Free
corollary. -/
theorem fermionTotalSpinZ_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalSpinZ N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalSpinZ
  refine Commute.smul_left ?_ _
  exact (fermionTotalUpNumber_commute_hubbardOnSiteInteraction N U).sub_left
    (fermionTotalDownNumber_commute_hubbardOnSiteInteraction N U)

/-! ## Spinful vacuum eigenstate corollaries

The JW vacuum on the underlying chain `Fin (2N+2)` is the
canonical spinful vacuum. All single-species vacuum results lift
mechanically. -/

/-- The spin-up annihilation operator at any site kills the
vacuum. -/
theorem fermionUpAnnihilation_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpAnnihilation N i).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 0)

/-- The spin-down annihilation operator at any site kills the
vacuum. -/
theorem fermionDownAnnihilation_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownAnnihilation N i).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 1)

/-- `n_{i,↑} · |vac⟩ = 0`. -/
theorem fermionUpNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiNumber_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 0)

/-- `n_{i,↓} · |vac⟩ = 0`. -/
theorem fermionDownNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownNumber N i).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiNumber_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 1)

/-- `N_↑ · |vac⟩ = 0`. -/
theorem fermionTotalUpNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalUpNumber N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionUpNumber_mulVec_vacuum N i)

/-- `N_↓ · |vac⟩ = 0`. -/
theorem fermionTotalDownNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalDownNumber N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionDownNumber_mulVec_vacuum N i)

/-- The vacuum is unpolarised: `S^z_tot · |vac⟩ = 0`. -/
theorem fermionTotalSpinZ_mulVec_vacuum (N : ℕ) :
    (fermionTotalSpinZ N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    fermionTotalUpNumber_mulVec_vacuum,
    fermionTotalDownNumber_mulVec_vacuum, sub_zero, smul_zero]

/-- The Hubbard kinetic operator annihilates the vacuum. -/
theorem hubbardKinetic_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (hubbardKinetic N t).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardKinetic
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiAnnihilation_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The Hubbard on-site interaction annihilates the vacuum. -/
theorem hubbardOnSiteInteraction_mulVec_vacuum (N : ℕ) (U : ℂ) :
    (hubbardOnSiteInteraction N U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.smul_mulVec]
  unfold fermionUpNumber fermionDownNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiNumber_mulVec_vacuum,
    Matrix.mulVec_zero, smul_zero]

/-- The full Hubbard Hamiltonian annihilates the vacuum. -/
theorem hubbardHamiltonian_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    (hubbardHamiltonian N t U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardHamiltonian
  rw [Matrix.add_mulVec, hubbardKinetic_mulVec_vacuum,
    hubbardOnSiteInteraction_mulVec_vacuum, add_zero]

end LatticeSystem.Fermion
