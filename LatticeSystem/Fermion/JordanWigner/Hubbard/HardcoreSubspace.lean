import LatticeSystem.Fermion.JordanWigner.Hubbard

/-!
# Hubbard hard-core subspace

This file starts the Tasaki §11.2 Nagaoka-ferromagnetism infrastructure.
The hard-core subspace is the finite-volume Hubbard subspace on which every
same-site double-occupancy operator `n_{i,↑} n_{i,↓}` vanishes. On this
subspace the on-site Hubbard interaction vanishes for every coupling `U`.

Tracked in Issue #4130. References: Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st edition, §11.2, pp. 381-388; this file
formalizes unnumbered no-double-occupancy infrastructure used before
Theorems 11.5 and 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Double occupancy and the hard-core subspace -/

/-- The same-site Hubbard double-occupancy operator
`n_{i,↑} n_{i,↓}` at spinful site `i`. -/
noncomputable def hubbardDoubleOccupancy (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionUpNumber N i * fermionDownNumber N i

/-- The finite-volume Hubbard hard-core subspace.

A vector is in this subspace exactly when every same-site double-occupancy
operator `n_{i,↑} n_{i,↓}` annihilates it. This is the unnumbered linear
subspace used in the infinite-`U` / one-hole Nagaoka sector before Tasaki
Theorems 11.5 and 11.7. -/
noncomputable def hubbardHardcoreSubspace (N : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) where
  carrier := {ψ | ∀ i : Fin (N + 1),
    (hubbardDoubleOccupancy N i).mulVec ψ = 0}
  zero_mem' := by
    intro i
    rw [Matrix.mulVec_zero]
  add_mem' := by
    intro ψ φ hψ hφ i
    rw [Matrix.mulVec_add, hψ i, hφ i, add_zero]
  smul_mem' := by
    intro a ψ hψ i
    rw [Matrix.mulVec_smul, hψ i, smul_zero]

/-- Membership in `hubbardHardcoreSubspace` is the vanishing of every
same-site double-occupancy operator. -/
theorem mem_hubbardHardcoreSubspace_iff
    (N : ℕ) {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ} :
    ψ ∈ hubbardHardcoreSubspace N ↔
      ∀ i : Fin (N + 1), (hubbardDoubleOccupancy N i).mulVec ψ = 0 := by
  rfl

/-- Each same-site double-occupancy operator annihilates a vector in the
Hubbard hard-core subspace. -/
theorem hubbardDoubleOccupancy_mulVec_eq_zero_of_mem_hardcore
    (N : ℕ) {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ hubbardHardcoreSubspace N) (i : Fin (N + 1)) :
    (hubbardDoubleOccupancy N i).mulVec ψ = 0 :=
  hψ i

/-! ## On-site interaction on the hard-core subspace -/

/-- The Hubbard on-site interaction annihilates every hard-core vector.

This is the algebraic no-double-occupancy reduction used at the start of
Tasaki §11.2 as unnumbered infrastructure for Theorems 11.5 and 11.7: if
every `n_{i,↑} n_{i,↓}` term is zero on `ψ`, then the finite sum
`U ∑ᵢ n_{i,↑} n_{i,↓}` is also zero on `ψ`. -/
theorem hubbardOnSiteInteraction_mulVec_eq_zero_of_mem_hardcore
    (N : ℕ) (U : ℂ) {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ hubbardHardcoreSubspace N) :
    (hubbardOnSiteInteraction N U).mulVec ψ = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  rw [Matrix.smul_mulVec]
  change U • (hubbardDoubleOccupancy N i).mulVec ψ = 0
  rw [hψ i, smul_zero]

/-- Pointwise form of
`hubbardOnSiteInteraction_mulVec_eq_zero_of_mem_hardcore`. -/
theorem hubbardOnSiteInteraction_apply_eq_zero_of_mem_hardcore
    (N : ℕ) (U : ℂ) {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ hubbardHardcoreSubspace N)
    (σ : Fin (2 * N + 2) → Fin 2) :
    (hubbardOnSiteInteraction N U).mulVec ψ σ = 0 := by
  rw [hubbardOnSiteInteraction_mulVec_eq_zero_of_mem_hardcore N U hψ]
  rfl

end LatticeSystem.Fermion
