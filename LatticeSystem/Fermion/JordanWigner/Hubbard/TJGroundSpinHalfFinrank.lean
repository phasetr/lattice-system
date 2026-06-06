import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundEnergyGe
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge

/-!
# Tasaki 11.5: the `Ŝ³=½` ground block is at most one-dimensional (Prop 11.24 PR-E3a)

`finrank ℂ (groundSubmoduleAtFilling Ĥ_tJ Ne ⊓ (Ŝ³ = ½)) ≤ 1`: the ground states in the `Ŝ³ = ½`
sector form a space of dimension at most one.  A ground state in that block is sector-supported, so
its coefficient vector is a complex eigenvector of the sector matrix at the ground energy
`μ = groundEnergyAtFilling`; the map `Φ ↦ tJExpansionCoeff Φ` is an injective `ℂ`-linear embedding of
the block into that eigenspace, whose dimension is `≤ 1` by Perron–Frobenius
(`matrix_complex_eigenspace_finrank_le_one_of_real`).

This is the upper-bound seed: combined with the SU(2) tower it bounds the full ground degeneracy by
`Ne+1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- `tJExpansionCoeff` packaged as a `ℂ`-linear map. -/
noncomputable def tJExpansionCoeffₗ (N Ne : ℕ) :
    ((Fin (2 * N + 2) → Fin 2) → ℂ) →ₗ[ℂ] (TJSpinHalfFillingSector N Ne → ℂ) where
  toFun := tJExpansionCoeff N Ne
  map_add' u u' := by
    funext s
    simp only [tJExpansionCoeff, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a u := by
    funext s
    simp only [tJExpansionCoeff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)

/-- A `Ŝ³=½`, `N̂=Ne`, hard-core eigenvector of `Ĥ_tJ` at real `E` has, as its coefficient vector, a
complex eigenvector of the (complexified) sector matrix at `E`. -/
theorem tJ_spinHalf_W_complexSectorEigen (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne) (τ J : ℝ)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) {Φ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hhc : Φ ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec Φ = (Ne : ℂ) • Φ)
    (hSz : (fermionTotalSpinZ N).mulVec Φ = ((1 / 2 : ℝ) : ℂ) • Φ)
    {E : ℝ} (hE : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec Φ = (E : ℂ) • Φ) :
    ((tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).map Complex.ofReal).mulVec
        (tJExpansionCoeff N Ne Φ) = (E : ℂ) • tJExpansionCoeff N Ne Φ := by
  have hsupp : Φ = tJExpansion N Ne (tJExpansionCoeff N Ne Φ) :=
    tJ_completeness Ne Φ (fun w hw =>
      tJ_mulVec_apply_eq_zero_of_not_sector Ne Φ hhc hN hSz w hw)
  set c := tJExpansionCoeff N Ne Φ with hcdef
  have hcoeff : (fun s' => ∑ s, c s *
      tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val) = (E : ℂ) • c := by
    have h1 := tJHamiltonian_mulVec_tJExpansion (cycleGraph (N + 1)) τ J Ne c
    rw [← hsupp, hE] at h1
    have h2 : tJExpansion N Ne ((E : ℂ) • c) =
        tJExpansion N Ne
          (fun s' => ∑ s, c s * tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val) := by
      rw [← h1, hsupp]
      unfold tJExpansion
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun s _ => by rw [Pi.smul_apply, smul_smul, smul_eq_mul])
    have hcc := congrArg (tJExpansionCoeff N Ne) h2
    rw [tJExpansionCoeff_tJExpansion, tJExpansionCoeff_tJExpansion] at hcc
    exact hcc.symm
  funext s'
  rw [show ((tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).map Complex.ofReal).mulVec c s'
      = (fun s' => ∑ s, c s * tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val) s' from ?_,
    hcoeff]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun s _ => by
    rw [tJEffMatrix_sector_eq_ofReal hpos Ne hodd τ J hτ hJ s' s]; ring)

/-- **The `Ŝ³ = ½` ground block has dimension at most one.** -/
theorem tJ_groundSubmodule_spinHalf_finrank_le_one (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) :
    finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin ((1 / 2 : ℝ) : ℂ)) ≤ 1 := by
  classical
  haveI : Fact (Ne < N + 1) := ⟨hNeLt⟩
  haveI : Fact (Odd Ne) := ⟨hodd⟩
  obtain ⟨c0, hc0⟩ : ∃ c : ℝ, ∀ q : TJSpinHalfFillingSector N Ne,
      tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q < c :=
    ⟨(Finset.univ.sup' Finset.univ_nonempty
        (fun q => tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q)) + 1,
      fun q => lt_of_le_of_lt
        (Finset.le_sup' (fun q => tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q)
          (Finset.mem_univ q)) (lt_add_one _)⟩
  obtain ⟨μ, v, hvpos, hveig, hmin, hfinrankR⟩ :=
    tJEffReMatrixOnSector_perronFrobenius hpos Ne hNeLt hodd τ J hτ hJ c0 hc0
  have hv0 : v ≠ 0 := fun h => by
    have := hvpos (Classical.arbitrary (TJSpinHalfFillingSector N Ne))
    rw [h] at this; simp at this
  have hgE : groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne = μ :=
    le_antisymm
      (tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen hpos Ne hodd τ J hτ.le hJ.le hv0 μ
        hveig)
      (tJ_groundEnergyAtFilling_ge_of_sectorMin hpos Ne hNeLt hodd τ J hτ.le hJ.le hmin)
  have hfinrankC : finrank ℂ ↥(Module.End.eigenspace (Matrix.toLin'
      ((tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).map Complex.ofReal)) (μ : ℂ)) ≤ 1 :=
    matrix_complex_eigenspace_finrank_le_one_of_real _ μ hfinrankR
  set blk := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin ((1 / 2 : ℝ) : ℂ) with hblk
  -- Each block element is `Ŝ³=½`, `N̂=Ne`, hard-core, and an `Ĥ_tJ`-eigenvector at `μ`.
  have hextract : ∀ Φ : ↥blk,
      (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec Φ.val = (μ : ℂ) • Φ.val ∧
      (fermionTotalNumber (2 * N + 1)).mulVec Φ.val = (Ne : ℂ) • Φ.val ∧
      Φ.val ∈ hubbardHardcoreSubspace N ∧
      (fermionTotalSpinZ N).mulVec Φ.val = ((1 / 2 : ℝ) : ℂ) • Φ.val := by
    intro Φ
    have hΦmem : Φ.val ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin ((1 / 2 : ℝ) : ℂ) := Φ.property
    simp only [groundSubmoduleAtFilling, Submodule.mem_inf, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hΦmem
    obtain ⟨⟨⟨hH, hNn⟩, hhc⟩, hsz⟩ := hΦmem
    exact ⟨by rw [← hgE]; exact hH, hNn, hhc, hsz⟩
  have hmem : ∀ Φ : ↥blk, ((tJExpansionCoeffₗ N Ne).comp blk.subtype) Φ ∈
      Module.End.eigenspace (Matrix.toLin'
        ((tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).map Complex.ofReal)) (μ : ℂ) := by
    intro Φ
    obtain ⟨hE, hNn, hhc, hsz⟩ := hextract Φ
    rw [Module.End.mem_eigenspace_iff, LinearMap.comp_apply, Submodule.subtype_apply,
      Matrix.toLin'_apply]
    exact tJ_spinHalf_W_complexSectorEigen hpos Ne hodd τ J hτ.le hJ.le hhc hNn hsz hE
  refine le_trans (LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict _ ((tJExpansionCoeffₗ N Ne).comp blk.subtype) hmem) ?_) hfinrankC
  intro Φ Φ' hΦΦ'
  have hcoeff : tJExpansionCoeff N Ne Φ.val = tJExpansionCoeff N Ne Φ'.val := by
    have := congrArg Subtype.val hΦΦ'
    simpa [LinearMap.codRestrict, LinearMap.comp_apply, tJExpansionCoeffₗ] using this
  have hsupp : ∀ Ψ : ↥blk, Ψ.val = tJExpansion N Ne (tJExpansionCoeff N Ne Ψ.val) := by
    intro Ψ
    obtain ⟨_, hNn, hhc, hsz⟩ := hextract Ψ
    exact tJ_completeness Ne Ψ.val (fun w hw =>
      tJ_mulVec_apply_eq_zero_of_not_sector Ne Ψ.val hhc hNn hsz w hw)
  exact Subtype.ext (by rw [hsupp Φ, hsupp Φ', hcoeff])

end LatticeSystem.Fermion
