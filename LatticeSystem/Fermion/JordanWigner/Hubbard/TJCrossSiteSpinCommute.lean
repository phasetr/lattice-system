import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Tasaki 11.5.3: cross-site commutators of annihilation operators with site-spin hops (Thm 11.26)

For `x ≠ y` a single annihilation operator at site `x` commutes through the two-fermion site-spin
operators at the different site `y` (they act on disjoint Jordan–Wigner orbitals):

* `fermionUpAnnihilation_commute_fermionSiteSpinPlus_of_ne` — `[ĉ_{x↑}, Ŝ⁺_y] = 0`;
* `fermionDownAnnihilation_commute_fermionSiteSpinMinus_of_ne` — `[ĉ_{x↓}, Ŝ⁻_y] = 0`.

These are the reordering inputs for the singlet-annihilation bond identity
`Δ_xy† Δ_xy = n̂_{x↑}n̂_{y↓} + n̂_{x↓}n̂_{y↑} − Ŝ⁺_x Ŝ⁻_y − Ŝ⁻_x Ŝ⁺_y` (and hence the
positive-semidefiniteness of the Heisenberg bond).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- For `x ≠ y`, `ĉ_{x↑}` commutes with `Ŝ⁺_y = ĉ†_{y↑} ĉ_{y↓}` (disjoint orbitals). -/
theorem fermionUpAnnihilation_commute_fermionSiteSpinPlus_of_ne
    (x y : Fin (N + 1)) (hxy : x ≠ y) :
    Commute (fermionUpAnnihilation N x) (fermionSiteSpinPlus N y) := by
  unfold fermionUpAnnihilation fermionSiteSpinPlus fermionUpCreation fermionDownAnnihilation
  have hac : fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 0) *
        fermionMultiCreation (2 * N + 1) (spinfulIndex N y 0) +
      fermionMultiCreation (2 * N + 1) (spinfulIndex N y 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 0) = 0 :=
    fermionMultiAnnihilation_creation_anticomm_of_ne
      (fun h => hxy (spinfulIndex_up_injective N h))
  have haa : fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 1) +
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 0) = 0 :=
    fermionMultiAnnihilation_anticomm_of_ne (spinfulIndex_up_ne_down N x y)
  unfold Commute SemiconjBy
  linear_combination (norm := noncomm_ring)
    hac * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 1) -
      fermionMultiCreation (2 * N + 1) (spinfulIndex N y 0) * haa

/-- For `x ≠ y`, `ĉ_{x↓}` commutes with `Ŝ⁻_y = ĉ†_{y↓} ĉ_{y↑}` (disjoint orbitals). -/
theorem fermionDownAnnihilation_commute_fermionSiteSpinMinus_of_ne
    (x y : Fin (N + 1)) (hxy : x ≠ y) :
    Commute (fermionDownAnnihilation N x) (fermionSiteSpinMinus N y) := by
  unfold fermionDownAnnihilation fermionSiteSpinMinus fermionDownCreation fermionUpAnnihilation
  have hac : fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1) *
        fermionMultiCreation (2 * N + 1) (spinfulIndex N y 1) +
      fermionMultiCreation (2 * N + 1) (spinfulIndex N y 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1) = 0 :=
    fermionMultiAnnihilation_creation_anticomm_of_ne
      (fun h => hxy (spinfulIndex_down_injective N h))
  have haa : fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 0) +
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1) = 0 :=
    fermionMultiAnnihilation_anticomm_of_ne (spinfulIndex_up_ne_down N y x).symm
  unfold Commute SemiconjBy
  linear_combination (norm := noncomm_ring)
    hac * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 0) -
      fermionMultiCreation (2 * N + 1) (spinfulIndex N y 1) * haa

end LatticeSystem.Fermion
