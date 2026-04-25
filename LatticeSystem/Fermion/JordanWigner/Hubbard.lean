/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Number
import LatticeSystem.Lattice.Graph
import Mathlib.Tactic.NoncommRing

/-!
# Hubbard model — core spinful operators (parent / content file)

This file (parent / content) contains the spinful (two-species) operator
wrappers, the on-site interaction / kinetic / Hamiltonian definitions,
and associated Hermiticity + `N̂`-commutativity.

Sub-files extending this module (tracked in #390):

| sub-file | content |
|---|---|
| `Hubbard/Charges.lean` | `N_↑`, `N_↓`, `S^z_tot`, vacuum eigenstates, |
|                        | cross-spin commutes |
| `Hubbard/Graph.lean` | graph-centric wrappers, open / periodic chain |
|                      | Hamiltonians + Gibbs states + companion families |

(Refactor Phase 2 PR 14 — final step of the JordanWigner 5-file
split, plan v4 §3.1. #390 sub-split into Charges + Graph sub-files.)
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Spinful (two-species) fermion operator wrappers

To realise true Hubbard / spinful fermion models we re-index a
single-species chain of length `2 * (N + 1)` as a chain of
`N + 1` spinful sites, with each site carrying a spin label
`σ : Fin 2`. The bijection `(i, σ) ↦ 2 * i + σ` puts the two
species at site `i` in the consecutive JW positions
`2 i` (spin up) and `2 i + 1` (spin down).

All algebraic facts about the two-species operators (CARs,
charge conservation, Hermiticity) follow for free from the
single-species results applied to the underlying chain. -/

/-- The spinful site index: `(i, σ) ↦ 2 * i + σ`. -/
def spinfulIndex (N : ℕ) (i : Fin (N + 1)) (σ : Fin 2) :
    Fin (2 * N + 2) :=
  ⟨2 * i.val + σ.val, by
    have hi : i.val < N + 1 := i.isLt
    have hσ : σ.val < 2 := σ.isLt
    omega⟩

/-- Spin-up annihilation operator at spinful site `i`:
the JW annihilation at the underlying single-species position
`2 * i`. -/
noncomputable def fermionUpAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down annihilation operator at spinful site `i`:
the JW annihilation at the underlying single-species position
`2 * i + 1`. -/
noncomputable def fermionDownAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 1)

/-- Spin-up creation operator at spinful site `i`. -/
noncomputable def fermionUpCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down creation operator at spinful site `i`. -/
noncomputable def fermionDownCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1)

/-- Spin-up site occupation number at spinful site `i`:
`n_{i,↑} = c_{i,↑}† · c_{i,↑}`. -/
noncomputable def fermionUpNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down site occupation number at spinful site `i`:
`n_{i,↓} = c_{i,↓}† · c_{i,↓}`. -/
noncomputable def fermionDownNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1)

/-- The on-site Hubbard interaction
`H_int = U Σ_i n_{i,↑} · n_{i,↓}` on the spinful chain. -/
noncomputable def hubbardOnSiteInteraction (N : ℕ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), U • (fermionUpNumber N i * fermionDownNumber N i)

/-- The Hubbard on-site interaction commutes with the total
particle-number operator `N̂` on the underlying chain (charge
conservation). -/
theorem hubbardOnSiteInteraction_commute_fermionTotalNumber
    (N : ℕ) (U : ℂ) :
    Commute (hubbardOnSiteInteraction N U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact (fermionDensityDensity_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).smul_left U

/-- The Hubbard on-site interaction is Hermitian when the coupling
`U` is real (`star U = U`). Each summand `n_{i,↑} · n_{i,↓}` is
Hermitian (commuting Hermitian factors), and the scalar `U`
preserves Hermiticity under the realness assumption. -/
theorem hubbardOnSiteInteraction_isHermitian
    (N : ℕ) {U : ℂ} (hU : star U = U) :
    (hubbardOnSiteInteraction N U).IsHermitian := by
  change (hubbardOnSiteInteraction N U)ᴴ = hubbardOnSiteInteraction N U
  unfold hubbardOnSiteInteraction
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_smul]
  unfold fermionUpNumber fermionDownNumber
  rw [(fermionMultiNumber_mul_isHermitian (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).eq, hU]

/-- The spin-symmetric tight-binding kinetic operator on the spinful
chain: `T = Σ_{σ} Σ_{i,j} t_{i,j} c_{i,σ}† c_{j,σ}`. Each spin
sector hops independently with the same coupling matrix `t`. -/
noncomputable def hubbardKinetic (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ σ : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    t i j • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))

/-- The spinful kinetic operator commutes with the total particle
number `N̂` on the underlying chain. Each summand
`t_{ij} • c_{iσ}† c_{jσ}` commutes with `N̂` via
`fermionTotalNumber_commute_hopping`, and finite sums preserve
this. -/
theorem hubbardKinetic_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (hubbardKinetic N t) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardKinetic
  refine Commute.sum_left _ _ _ (fun σ _ => ?_)
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact ((fermionTotalNumber_commute_hopping (2 * N + 1)
    (spinfulIndex N i σ) (spinfulIndex N j σ)).symm).smul_left (t i j)

/-- The spinful kinetic operator is Hermitian when the hopping
matrix `t` is Hermitian (`star (t i j) = t j i`). For each fixed
spin `σ`, the inner double sum is the single-species
`fermionHopping (2N+1) t̃` for the lifted coupling
`t̃ (spinfulIndex N i σ) (spinfulIndex N j σ) = t i j`; we prove
Hermiticity term-by-term using the conjTranspose flip and a
`Finset.sum_comm` index swap. -/
theorem hubbardKinetic_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i) :
    (hubbardKinetic N t).IsHermitian := by
  change (hubbardKinetic N t)ᴴ = hubbardKinetic N t
  unfold hubbardKinetic
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  calc (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), t i j •
          (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)))ᴴ
      = ∑ i, (∑ j, t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)))ᴴ := by
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, (t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)))ᴴ := by
        congr 1; funext i
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, t j i •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N j σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N i σ)) := by
        congr 1; funext i; congr 1; funext j
        rw [Matrix.conjTranspose_smul,
          fermionHoppingTerm_conjTranspose, ht]
    _ = ∑ j, ∑ i, t j i •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N j σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N i σ)) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)) := rfl

/-- The canonical (single-band) Hubbard Hamiltonian:
`H = Σ_{σ} Σ_{i,j} t_{i,j} c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}`. -/
noncomputable def hubbardHamiltonian (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N t + hubbardOnSiteInteraction N U

/-- The Hubbard Hamiltonian commutes with the total particle
number `N̂`: charge conservation. Direct from
`hubbardKinetic_commute_fermionTotalNumber` and
`hubbardOnSiteInteraction_commute_fermionTotalNumber` via
`Commute.add_left`. -/
theorem hubbardHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardHamiltonian N t U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHamiltonian
  exact (hubbardKinetic_commute_fermionTotalNumber N t).add_left
    (hubbardOnSiteInteraction_commute_fermionTotalNumber N U)

/-- The Hubbard Hamiltonian is Hermitian when the hopping matrix
`t` is Hermitian and the on-site coupling `U` is real. -/
theorem hubbardHamiltonian_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardHamiltonian N t U).IsHermitian := by
  unfold hubbardHamiltonian
  exact (hubbardKinetic_isHermitian N ht).add
    (hubbardOnSiteInteraction_isHermitian N hU)

/-- The Gibbs state of the canonical Hubbard Hamiltonian. -/
noncomputable def hubbardGibbsState
    (N : ℕ) (β : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardHamiltonian N t U)

/-- The Hubbard Gibbs state is Hermitian when `t` is Hermitian and
`U` is real. -/
theorem hubbardGibbsState_isHermitian
    (N : ℕ) (β : ℝ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardGibbsState N β t U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardHamiltonian_isHermitian N ht hU) β

/-- The Hubbard Gibbs state commutes with the Hubbard Hamiltonian
(generic instance of `gibbsState_commute_hamiltonian`). -/
theorem hubbardGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardGibbsState N β t U) (hubbardHamiltonian N t U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _


end LatticeSystem.Fermion
