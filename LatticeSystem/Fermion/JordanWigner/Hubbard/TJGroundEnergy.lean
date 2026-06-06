import LatticeSystem.Fermion.JordanWigner.Hubbard.TJEigenvectorLift
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorGroundState
import LatticeSystem.Fermion.JordanWigner.Hubbard.GroundSubspaceAtFilling

/-!
# Tasaki 11.5: variational bound on the t-J ground energy (Prop 11.24 PR-E2, `≤` direction)

The lifted Perron–Frobenius eigenvector `tJExpansion c` is an admissible state of the fixed-filling
hard-core variational problem (it is a no-double-occupancy `N̂ = Ne` eigenvector of `Ĥ_tJ`), so its
energy `μ` (the lowest sector-matrix eigenvalue) bounds the ground energy from above:
`groundEnergyAtFilling Ĥ_tJ Ne ≤ μ` (`tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen`).

This is the easy half of the E2 ground-energy identification `groundEnergyAtFilling = μ`; the reverse
`μ ≤ groundEnergyAtFilling` (the global minimum sits in the `Ŝ³ = ½` block, via A.17 and odd `Ne`)
follows next.  Together they make the lifted PF eigenvector a genuine ground state.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- A sector expansion lies in the hard-core subspace (a sum of hard-core basis states). -/
theorem tJExpansion_mem_hardcore (Ne : ℕ) (v : TJSpinHalfFillingSector N Ne → ℂ) :
    tJExpansion N Ne v ∈ hubbardHardcoreSubspace N := by
  unfold tJExpansion
  exact Submodule.sum_mem _
    (fun s _ => Submodule.smul_mem _ _ (tJConfigOf_mem_hardcore N s.val))

/-- A sector expansion is an `N̂ = Ne` eigenvector (each sector basis state has electron number
`Ne`). -/
theorem fermionTotalNumber_mulVec_tJExpansion (Ne : ℕ) (v : TJSpinHalfFillingSector N Ne → ℂ) :
    (fermionTotalNumber (2 * N + 1)).mulVec (tJExpansion N Ne v) =
      (Ne : ℂ) • tJExpansion N Ne v := by
  unfold tJExpansion
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.mulVec_smul, fermionTotalNumber_mulVec_tJConfigOf_eq N s.val Ne s.property.2,
    smul_comm]

/-- The coefficient functional vanishes on the zero vector. -/
theorem tJExpansionCoeff_zero (Ne : ℕ) :
    tJExpansionCoeff N Ne (0 : (Fin (2 * N + 2) → Fin 2) → ℂ) = 0 := by
  funext s
  unfold tJExpansionCoeff
  simp

/-- A nonzero coefficient vector gives a nonzero sector expansion (the expansion is injective, with
left inverse `tJExpansionCoeff`). -/
theorem tJExpansion_ne_zero_of_ne_zero (Ne : ℕ) {v : TJSpinHalfFillingSector N Ne → ℂ}
    (hv : v ≠ 0) : tJExpansion N Ne v ≠ 0 := by
  intro h
  apply hv
  have hinv := tJExpansionCoeff_tJExpansion (N := N) Ne v
  rw [h, tJExpansionCoeff_zero] at hinv
  exact hinv.symm

/-- **Variational bound on the t-J ground energy (E2, `≤`).** A nonzero real sector eigenvector `c`
of `tJEffReMatrixOnSector` at eigenvalue `μ` lifts to an admissible state whose energy is `μ`, so
`groundEnergyAtFilling Ĥ_tJ Ne ≤ μ`. -/
theorem tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) {c : TJSpinHalfFillingSector N Ne → ℝ} (hc : c ≠ 0) (μ : ℝ)
    (heig : (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ c = μ • c) :
    groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ≤ μ := by
  have hcc0 : (fun s => (c s : ℂ)) ≠ (0 : TJSpinHalfFillingSector N Ne → ℂ) := by
    intro h; apply hc; funext s
    have hs := congrFun h s
    simp only [Pi.zero_apply] at hs
    exact_mod_cast hs
  exact groundEnergyAtFilling_le_of_eigenvector (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne
    (tJExpansion_ne_zero_of_ne_zero Ne hcc0) μ
    (fermionTotalNumber_mulVec_tJExpansion Ne _) (tJExpansion_mem_hardcore Ne _)
    (tJHamiltonian_mulVec_tJExpansion_ofReal hpos Ne hodd τ J hτ hJ c μ heig)

end LatticeSystem.Fermion
