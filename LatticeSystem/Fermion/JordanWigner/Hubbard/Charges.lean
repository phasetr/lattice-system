import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore

/-!
# Spinful conserved charges, vacuum eigenstates, and cross-spin commutes

Extracted from `JordanWigner/Hubbard.lean` (tracked in #390). This sub-file
contains:

1. **Spinful conserved charges** — `N_↑`, `N_↓`, `S^z_tot` and their pairwise
   commutativity with each other and with `N̂`.
2. **Vacuum eigenstate corollaries** — annihilation operators, number operators,
   kinetic and on-site terms all annihilate the JW vacuum.
3. **Cross-spin commutes** — `N_↓` commutes with the up-sector, `N_↑` commutes
   with the down-sector.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Cross-spin commutes (different species commute) -/

/-- Even and odd JW positions are distinct: `spinfulIndex N i 0 ≠
spinfulIndex N j 1` (the up-channel position `2 i` is never the
down-channel position `2 j + 1`). -/
theorem spinfulIndex_up_ne_down (N : ℕ) (i j : Fin (N + 1)) :
    spinfulIndex N i 0 ≠ spinfulIndex N j 1 := by
  intro heq
  have h := congrArg Fin.val heq
  change False
  simp [spinfulIndex] at h
  omega

/-- `N_↓` commutes with every `c_{i,↑}†`: each summand
`n_{2k+1}` and `c_{2i}†` are at distinct JW positions. -/
theorem fermionTotalDownNumber_commute_fermionUpCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpCreation N i) := by
  unfold fermionTotalDownNumber fermionUpCreation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiCreation_of_ne
    ((spinfulIndex_up_ne_down N i k).symm).symm.symm

/-- `N_↓` commutes with every `c_{i,↑}`. -/
theorem fermionTotalDownNumber_commute_fermionUpAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpAnnihilation N i) := by
  unfold fermionTotalDownNumber fermionUpAnnihilation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    ((spinfulIndex_up_ne_down N i k).symm).symm.symm

/-- `N_↓` commutes with every `n_{i,↑}` (number operators always
commute, but here we record the cross-spin special case
explicitly). -/
theorem fermionTotalDownNumber_commute_fermionUpNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpNumber N i) := by
  unfold fermionTotalDownNumber fermionUpNumber
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N k 1) (spinfulIndex N i 0)

/-- `N_↑` commutes with every `c_{i,↓}†`. -/
theorem fermionTotalUpNumber_commute_fermionDownCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownCreation N i) := by
  unfold fermionTotalUpNumber fermionDownCreation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiCreation_of_ne
    (spinfulIndex_up_ne_down N k i)

/-- `N_↑` commutes with every `c_{i,↓}`. -/
theorem fermionTotalUpNumber_commute_fermionDownAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownAnnihilation N i) := by
  unfold fermionTotalUpNumber fermionDownAnnihilation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    (spinfulIndex_up_ne_down N k i)

/-- `N_↑` commutes with every `n_{i,↓}`. -/
theorem fermionTotalUpNumber_commute_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownNumber N i) := by
  unfold fermionTotalUpNumber fermionDownNumber
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the up-sector hopping term
`c_{i,↑}† · c_{j,↑}` (cross-spin). -/
theorem fermionTotalDownNumber_commute_upHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N)
      (fermionUpCreation N i * fermionUpAnnihilation N j) :=
  (fermionTotalDownNumber_commute_fermionUpCreation N i).mul_right
    (fermionTotalDownNumber_commute_fermionUpAnnihilation N j)

/-- `N_↑` commutes with the down-sector hopping term
`c_{i,↓}† · c_{j,↓}` (cross-spin). -/
theorem fermionTotalUpNumber_commute_downHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N)
      (fermionDownCreation N i * fermionDownAnnihilation N j) :=
  (fermionTotalUpNumber_commute_fermionDownCreation N i).mul_right
    (fermionTotalUpNumber_commute_fermionDownAnnihilation N j)

end LatticeSystem.Fermion
