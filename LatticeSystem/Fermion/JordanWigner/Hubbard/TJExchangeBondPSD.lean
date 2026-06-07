import LatticeSystem.Fermion.JordanWigner.Hubbard.TJCrossSiteSpinCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSingletAnnihilation
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingExchange

/-!
# Tasaki 11.5.3: the Heisenberg bond is positive-semidefinite (Theorem 11.26 PR3c)

The two-site Heisenberg bond equals `½ Δ_xy† Δ_xy` for the singlet annihilation operator
`Δ_xy = ĉ_{y↓}ĉ_{x↑} − ĉ_{y↑}ĉ_{x↓}` (a global operator identity, `x ≠ y`).  This file proves the
underlying CAR identity:

* `tJSingletAnnihilation_conjTranspose_mul_self` —
  `Δ_xy† Δ_xy = n̂_{x↑}n̂_{y↓} + n̂_{x↓}n̂_{y↑} − Ŝ⁺_x Ŝ⁻_y − Ŝ⁻_x Ŝ⁺_y` (`x ≠ y`), by expanding the
  four products and reordering with the cross-site (anti)commutators.

The half-bond identity `n̂_x n̂_y/4 − Ŝ_x·Ŝ_y = ½ Δ_xy† Δ_xy` and the resulting
positive-semidefiniteness (the input to the half-filling ground energy) follow in a follow-up.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- `n̂_{y↓}` (as `ĉ†_{y↓}ĉ_{y↓}`) commutes with `ĉ_{x↑}` (disjoint orbitals, always). -/
private theorem fermionDownNumber_commute_fermionUpAnnihilation (x y : Fin (N + 1)) :
    Commute (fermionDownNumber N y) (fermionUpAnnihilation N x) := by
  unfold fermionDownNumber fermionUpAnnihilation
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    (spinfulIndex_up_ne_down N x y).symm

/-- `n̂_{y↑}` (as `ĉ†_{y↑}ĉ_{y↑}`) commutes with `ĉ_{x↓}` (disjoint orbitals, always). -/
private theorem fermionUpNumber_commute_fermionDownAnnihilation (x y : Fin (N + 1)) :
    Commute (fermionUpNumber N y) (fermionDownAnnihilation N x) := by
  unfold fermionUpNumber fermionDownAnnihilation
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne (spinfulIndex_up_ne_down N y x)

/-- **The bond CAR identity.**  `Δ_xy† Δ_xy = n̂_{x↑}n̂_{y↓} + n̂_{x↓}n̂_{y↑} − Ŝ⁺_x Ŝ⁻_y −
Ŝ⁻_x Ŝ⁺_y` for `x ≠ y`: expand the four products and reorder via the cross-site
(anti)commutators. -/
theorem tJSingletAnnihilation_conjTranspose_mul_self (x y : Fin (N + 1)) (hxy : x ≠ y) :
    (tJSingletAnnihilation N x y)ᴴ * tJSingletAnnihilation N x y =
      fermionUpNumber N x * fermionDownNumber N y + fermionDownNumber N x * fermionUpNumber N y -
        fermionSiteSpinPlus N x * fermionSiteSpinMinus N y -
        fermionSiteSpinMinus N x * fermionSiteSpinPlus N y := by
  rw [tJSingletAnnihilation_conjTranspose, tJSingletAnnihilation]
  have hT1 : fermionUpCreation N x * fermionDownCreation N y *
      (fermionDownAnnihilation N y * fermionUpAnnihilation N x) =
      fermionUpNumber N x * fermionDownNumber N y :=
    calc fermionUpCreation N x * fermionDownCreation N y *
          (fermionDownAnnihilation N y * fermionUpAnnihilation N x)
        = fermionUpCreation N x * (fermionDownNumber N y * fermionUpAnnihilation N x) := by
          rw [show fermionDownNumber N y = fermionDownCreation N y * fermionDownAnnihilation N y
            from rfl]; noncomm_ring
      _ = fermionUpCreation N x * (fermionUpAnnihilation N x * fermionDownNumber N y) := by
          rw [(fermionDownNumber_commute_fermionUpAnnihilation x y).eq]
      _ = fermionUpNumber N x * fermionDownNumber N y := by
          rw [show fermionUpNumber N x = fermionUpCreation N x * fermionUpAnnihilation N x
            from rfl]; noncomm_ring
  have hT4 : fermionDownCreation N x * fermionUpCreation N y *
      (fermionUpAnnihilation N y * fermionDownAnnihilation N x) =
      fermionDownNumber N x * fermionUpNumber N y :=
    calc fermionDownCreation N x * fermionUpCreation N y *
          (fermionUpAnnihilation N y * fermionDownAnnihilation N x)
        = fermionDownCreation N x * (fermionUpNumber N y * fermionDownAnnihilation N x) := by
          rw [show fermionUpNumber N y = fermionUpCreation N y * fermionUpAnnihilation N y
            from rfl]; noncomm_ring
      _ = fermionDownCreation N x * (fermionDownAnnihilation N x * fermionUpNumber N y) := by
          rw [(fermionUpNumber_commute_fermionDownAnnihilation x y).eq]
      _ = fermionDownNumber N x * fermionUpNumber N y := by
          rw [show fermionDownNumber N x = fermionDownCreation N x * fermionDownAnnihilation N x
            from rfl]; noncomm_ring
  have hT2 : fermionUpCreation N x * fermionDownCreation N y *
      (fermionUpAnnihilation N y * fermionDownAnnihilation N x) =
      fermionSiteSpinPlus N x * fermionSiteSpinMinus N y :=
    calc fermionUpCreation N x * fermionDownCreation N y *
          (fermionUpAnnihilation N y * fermionDownAnnihilation N x)
        = fermionUpCreation N x * (fermionSiteSpinMinus N y * fermionDownAnnihilation N x) := by
          rw [show fermionSiteSpinMinus N y = fermionDownCreation N y * fermionUpAnnihilation N y
            from rfl]; noncomm_ring
      _ = fermionUpCreation N x * (fermionDownAnnihilation N x * fermionSiteSpinMinus N y) := by
          rw [← (fermionDownAnnihilation_commute_fermionSiteSpinMinus_of_ne x y hxy).eq]
      _ = fermionSiteSpinPlus N x * fermionSiteSpinMinus N y := by
          rw [show fermionSiteSpinPlus N x = fermionUpCreation N x * fermionDownAnnihilation N x
            from rfl]; noncomm_ring
  have hT3 : fermionDownCreation N x * fermionUpCreation N y *
      (fermionDownAnnihilation N y * fermionUpAnnihilation N x) =
      fermionSiteSpinMinus N x * fermionSiteSpinPlus N y :=
    calc fermionDownCreation N x * fermionUpCreation N y *
          (fermionDownAnnihilation N y * fermionUpAnnihilation N x)
        = fermionDownCreation N x * (fermionSiteSpinPlus N y * fermionUpAnnihilation N x) := by
          rw [show fermionSiteSpinPlus N y = fermionUpCreation N y * fermionDownAnnihilation N y
            from rfl]; noncomm_ring
      _ = fermionDownCreation N x * (fermionUpAnnihilation N x * fermionSiteSpinPlus N y) := by
          rw [← (fermionUpAnnihilation_commute_fermionSiteSpinPlus_of_ne x y hxy).eq]
      _ = fermionSiteSpinMinus N x * fermionSiteSpinPlus N y := by
          rw [show fermionSiteSpinMinus N x = fermionDownCreation N x * fermionUpAnnihilation N x
            from rfl]; noncomm_ring
  rw [sub_mul, mul_sub, mul_sub, hT1, hT2, hT3, hT4]
  noncomm_ring

end LatticeSystem.Fermion
