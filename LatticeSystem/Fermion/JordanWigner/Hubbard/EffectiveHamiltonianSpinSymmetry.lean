import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism

/-!
# SU(2) symmetry of the Hubbard effective Hamiltonian

This file lifts the full SU(2) spin symmetry of the Hubbard Hamiltonian
(`[Ĥ, Ŝ^±_tot] = 0`, Tasaki §9.3.3) to the one-hole effective Hamiltonian
`Ĥ_eff = P̂_hc Ĥ P̂_hc` of §11.2. The key new ingredient is that the hard-core
projection commutes with the total spin raising/lowering operators, because the
spin operators preserve the no-double-occupancy subspace (each `Ŝ^+_tot` term
`ĉ†_{k,↑} ĉ_{k,↓}` commutes with every double-occupancy operator
`n_{i,↑} n_{i,↓}`).

The SU(2) symmetry of `Ĥ_eff` is the structural reason behind the
`(2 S_max + 1)`-fold degeneracy in the weak Nagaoka theorem (Theorem 11.5):
applying `Ŝ^-_tot` to a ferromagnetic ground state produces the full spin
multiplet of degenerate ground states.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §9.3.3 and §11.2.1, pp. 332, 384.
-/

namespace LatticeSystem.Fermion

open Matrix

/-! ## The spin operators commute with the hard-core projection -/

/-- The total spin raising operator commutes with each same-site
double-occupancy operator. -/
theorem fermionTotalSpinPlus_commute_hubbardDoubleOccupancy (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N) (hubbardDoubleOccupancy N i) := by
  unfold fermionTotalSpinPlus hubbardDoubleOccupancy
  apply Commute.sum_left
  intro k _
  exact fermionSpinPlusTerm_commute_interactionTerm N k i

/-- The total spin raising operator commutes with each hard-core factor
`1 - n_{i,↑} n_{i,↓}`. -/
theorem fermionTotalSpinPlus_commute_hubbardHardcoreFactor (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N) (hubbardHardcoreFactor N i) := by
  unfold hubbardHardcoreFactor
  exact (Commute.one_right _).sub_right
    (fermionTotalSpinPlus_commute_hubbardDoubleOccupancy N i)

/-- The total spin raising operator commutes with the hard-core projection
`P̂_hc = ∏_i (1 - n_{i,↑} n_{i,↓})`: the spin operators preserve the
no-double-occupancy subspace. -/
theorem fermionTotalSpinPlus_commute_hubbardHardcoreProjection (N : ℕ) :
    Commute (fermionTotalSpinPlus N) (hubbardHardcoreProjection N) := by
  unfold hubbardHardcoreProjection
  exact Finset.noncommProd_commute _ _ _ _
    (fun i _ => fermionTotalSpinPlus_commute_hubbardHardcoreFactor N i)

/-! ## SU(2) symmetry of the effective Hamiltonian -/

/-- `[Ĥ_eff, Ŝ^+_tot] = 0`: the effective Hamiltonian inherits the SU(2)
raising symmetry, since `Ŝ^+_tot` commutes with both `Ĥ` and the hard-core
projection. -/
theorem fermionTotalSpinPlus_commute_hubbardEffectiveHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (fermionTotalSpinPlus N) (hubbardEffectiveHamiltonian N t U) := by
  unfold hubbardEffectiveHamiltonian
  exact ((fermionTotalSpinPlus_commute_hubbardHardcoreProjection N).mul_right
    (fermionTotalSpinPlus_commute_hubbardHamiltonian N t U)).mul_right
    (fermionTotalSpinPlus_commute_hubbardHardcoreProjection N)

/-- `[Ĥ_eff, Ŝ^-_tot] = 0`: derived from the raising version by taking adjoints,
using that `Ĥ_eff` is Hermitian and `(Ŝ^+_tot)ᴴ = Ŝ^-_tot`. -/
theorem fermionTotalSpinMinus_commute_hubbardEffectiveHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    Commute (fermionTotalSpinMinus N) (hubbardEffectiveHamiltonian N t U) := by
  have h_plus :=
    (fermionTotalSpinPlus_commute_hubbardEffectiveHamiltonian N t U).eq
  have h_He := hubbardEffectiveHamiltonian_isHermitian N hJ hU
  have h_adj := congrArg Matrix.conjTranspose h_plus
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose N,
    h_He.eq] at h_adj
  exact h_adj.symm

/-! ## Conservation of total spin -/

/-- `Ŝ^z_tot` commutes with each same-site double-occupancy operator (all number
operators commute). -/
theorem fermionTotalSpinZ_commute_hubbardDoubleOccupancy (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (hubbardDoubleOccupancy N i) := by
  unfold fermionTotalSpinZ hubbardDoubleOccupancy fermionTotalUpNumber
    fermionTotalDownNumber fermionUpNumber fermionDownNumber
  refine Commute.smul_left ?_ _
  refine Commute.sub_left ?_ ?_ <;>
    refine Commute.sum_left _ _ _ (fun k _ => ?_) <;>
    exact (fermionMultiNumber_commute (2 * N + 1) _ (spinfulIndex N i 0)).mul_right
      (fermionMultiNumber_commute (2 * N + 1) _ (spinfulIndex N i 1))

/-- `Ŝ^z_tot` commutes with each hard-core factor. -/
theorem fermionTotalSpinZ_commute_hubbardHardcoreFactor (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalSpinZ N) (hubbardHardcoreFactor N i) := by
  unfold hubbardHardcoreFactor
  exact (Commute.one_right _).sub_right
    (fermionTotalSpinZ_commute_hubbardDoubleOccupancy N i)

/-- `Ŝ^z_tot` commutes with the hard-core projection. -/
theorem fermionTotalSpinZ_commute_hubbardHardcoreProjection (N : ℕ) :
    Commute (fermionTotalSpinZ N) (hubbardHardcoreProjection N) := by
  unfold hubbardHardcoreProjection
  exact Finset.noncommProd_commute _ _ _ _
    (fun i _ => fermionTotalSpinZ_commute_hubbardHardcoreFactor N i)

/-- `[Ĥ_eff, Ŝ^z_tot] = 0`. -/
theorem fermionTotalSpinZ_commute_hubbardEffectiveHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (fermionTotalSpinZ N) (hubbardEffectiveHamiltonian N t U) := by
  unfold hubbardEffectiveHamiltonian
  exact ((fermionTotalSpinZ_commute_hubbardHardcoreProjection N).mul_right
    (fermionTotalSpinZ_commute_hubbardHamiltonian N t U)).mul_right
    (fermionTotalSpinZ_commute_hubbardHardcoreProjection N)

/-- `[Ĥ_eff, (Ŝ_tot)²] = 0`: the effective Hamiltonian conserves total spin, so
its eigenspaces split into fixed-`S_tot` sectors. This is the conservation law
underlying the `S_tot = S_max` statement of the weak Nagaoka theorem (11.5) and
the per-sector Perron–Frobenius analysis of the full theorem (11.7). -/
theorem fermionTotalSpinSquared_commute_hubbardEffectiveHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    Commute (fermionTotalSpinSquared N) (hubbardEffectiveHamiltonian N t U) := by
  unfold fermionTotalSpinSquared
  have hz := fermionTotalSpinZ_commute_hubbardEffectiveHamiltonian N t U
  refine Commute.add_left
    ((fermionTotalSpinMinus_commute_hubbardEffectiveHamiltonian N t U hJ hU).mul_left
      (fermionTotalSpinPlus_commute_hubbardEffectiveHamiltonian N t U)) ?_
  exact hz.mul_left (hz.add_left (Commute.one_left _))

end LatticeSystem.Fermion
