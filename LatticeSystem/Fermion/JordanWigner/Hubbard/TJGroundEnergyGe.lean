import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingSpinZDiag
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingCompressSpinAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundEnergyReverse
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorGroundState
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHermitian
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Math.AngularMomentum.SpinHalfSector

/-!
# Tasaki 11.5: the Perron–Frobenius minimum bounds the ground energy (Prop 11.24 PR-E2 ≥)

The W-restricted A.17 capstone: the minimum eigenvalue `E0' = hermitianMinEigenvalue Ĥ_W` of the
compressed Hamiltonian has, by the matrix Theorem A.17 (whose hypotheses are the compressed
Hermitian/su(2)/commute relations), an eigenstate in the `Ŝ³ = ½` sector (odd `Ne` kills the
`Ŝ³ = 0` branch).  Lifting it to a genuine `W`-eigenstate of `Ĥ_tJ` and feeding the Perron–Frobenius
minimality gives `μ ≤ E0'` (`tJ_perronFrobeniusMin_le_hermitianMinEigenvalue`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443; Appendix A.3.2 Theorem A.17.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-- **`μ ≤ hermitianMinEigenvalue Ĥ_W`.** The Perron–Frobenius sector minimum `μ` is at most the
minimum eigenvalue of the compressed Hamiltonian `Ĥ_W = compress Ĥ_tJ`: A.17 places an `Ĥ_W`-min
eigenstate in the `Ŝ³ = ½` sector (odd `Ne`), and lifting it back to `W` + PF minimality bounds `μ`
by that eigenvalue. -/
theorem tJ_perronFrobeniusMin_le_hermitianMinEigenvalue (hpos : 0 < N) (Ne : ℕ)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) [Nonempty (TJFillingSector N Ne)] {μ : ℝ}
    (hμmin : ∀ (lam : ℝ) (w : TJSpinHalfFillingSector N Ne → ℝ), w ≠ 0 →
      (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ w = lam • w → μ ≤ lam) :
    μ ≤ hermitianMinEigenvalue (tJFillingCompress_isHermitian (N := N) Ne
      (tJHamiltonian_isHermitian N (cycleGraph (N + 1)) τ J)) := by
  classical
  set hHW := tJFillingCompress_isHermitian (N := N) Ne
    (tJHamiltonian_isHermitian N (cycleGraph (N + 1)) τ J) with hHWdef
  obtain ⟨ψ, hψunit, hψeig⟩ := exists_unit_eigenvector_hermitianMinEigenvalue hHW
  have hψ0 : ψ ≠ 0 := by intro h; rw [h] at hψunit; simp at hψunit
  obtain ⟨Φ, hΦ0, hΦeig, hΦspin⟩ := LatticeSystem.Math.ham_eigenstate_spin_zero_or_half
    (tJFillingCompress N Ne (tJHamiltonian N (cycleGraph (N + 1)) τ J))
    (tJFillingCompress N Ne (tJTotalSpinOne N))
    (tJFillingCompress N Ne (tJTotalSpinTwo N))
    (tJFillingCompress N Ne (fermionTotalSpinZ N))
    hHW
    (tJFillingCompress_isHermitian Ne (tJTotalSpinOne_isHermitian N))
    (tJFillingCompress_isHermitian Ne (tJTotalSpinTwo_isHermitian N))
    (tJFillingCompress_isHermitian Ne (fermionTotalSpinZ_isHermitian N))
    (tJFillingCompress_tJHamiltonian_commute_one Ne (cycleGraph (N + 1)) τ J)
    (tJFillingCompress_tJHamiltonian_commute_two Ne (cycleGraph (N + 1)) τ J)
    (tJFillingCompress_tJHamiltonian_commute_three Ne (cycleGraph (N + 1)) τ J)
    (tJFillingCompress_su2_12 Ne) (tJFillingCompress_su2_23 Ne) (tJFillingCompress_su2_31 Ne)
    hψ0 hψeig
  have hTΦ0 : tJFillingExpansion N Ne Φ ≠ 0 := by
    intro h
    apply hΦ0
    have hinv := tJFillingExpansionCoeff_tJFillingExpansion Ne Φ
    rw [h, tJFillingExpansionCoeff_zero] at hinv
    exact hinv.symm
  have hmemW := tJFillingExpansion_mem_tJFillingWSubmodule Ne Φ
  rw [mem_tJFillingWSubmodule_iff] at hmemW
  have hHeig : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec (tJFillingExpansion N Ne Φ)
      = ((hermitianMinEigenvalue hHW : ℝ) : ℂ) • tJFillingExpansion N Ne Φ :=
    mulVec_tJFillingExpansion_of_compress_eigen Ne
      (preservesTJFillingW_tJHamiltonian Ne (cycleGraph (N + 1)) τ J) hΦeig
  have hSzhalf : (fermionTotalSpinZ N).mulVec (tJFillingExpansion N Ne Φ)
      = ((1 / 2 : ℝ) : ℂ) • tJFillingExpansion N Ne Φ := by
    rcases hΦspin with h0 | hhalf
    · exfalso
      apply hΦ0
      have hlift : (fermionTotalSpinZ N).mulVec (tJFillingExpansion N Ne Φ) = 0 := by
        rw [mulVec_tJFillingExpansion_of_compress_eigen Ne
          (preservesTJFillingW_fermionTotalSpinZ Ne) (h0.trans (zero_smul ℂ Φ).symm), zero_smul]
      exact tJFillingExpansion_eq_zero_of_spinZ_mulVec_eq_zero Ne hodd hlift
    · exact mulVec_tJFillingExpansion_of_compress_eigen Ne
        (preservesTJFillingW_fermionTotalSpinZ Ne) hhalf
  exact tJ_sectorMin_le_of_spinHalf_W_eigenvalue hpos Ne hodd τ J hτ hJ hμmin hTΦ0 hmemW.2 hmemW.1
    hSzhalf hHeig

/-- **`μ ≤ groundEnergyAtFilling`.** Every admissible `(N̂=Ne, hard-core)` unit state has energy at
least `hermitianMinEigenvalue Ĥ_W ≥ μ`: its energy equals the matrix Rayleigh quotient of its
coefficient vector (Rayleigh bridge + isometry), bounded below by `hermitianMinEigenvalue Ĥ_W` by the
variational principle, and `μ ≤ hermitianMinEigenvalue Ĥ_W`. -/
theorem tJ_groundEnergyAtFilling_ge_of_sectorMin (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) {μ : ℝ}
    (hμmin : ∀ (lam : ℝ) (w : TJSpinHalfFillingSector N Ne → ℝ), w ≠ 0 →
      (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ w = lam • w → μ ≤ lam) :
    μ ≤ groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne := by
  classical
  haveI : Fact (Ne < N + 1) := ⟨hNeLt⟩
  haveI : Fact (Odd Ne) := ⟨hodd⟩
  haveI hNE : Nonempty (TJFillingSector N Ne) :=
    (tJSpinHalfFillingSector_nonempty (N := N) Ne).map (fun s => ⟨s.val, s.property.2⟩)
  set hHW := tJFillingCompress_isHermitian (N := N) Ne
    (tJHamiltonian_isHermitian N (cycleGraph (N + 1)) τ J) with hHWdef
  have hμE0 : μ ≤ hermitianMinEigenvalue hHW :=
    tJ_perronFrobeniusMin_le_hermitianMinEigenvalue hpos Ne hodd τ J hτ hJ hμmin
  -- the filling space `W` is nonempty as a set of unit states (a basis state)
  haveI : Nonempty (fillingHardcoreStates N Ne) := by
    refine ⟨⟨(WithLp.equiv 2 _).symm (basisVec (tJConfigOf N (Classical.choice hNE).val)), ?_, ?_, ?_⟩⟩
    · rw [EuclideanSpace.norm_eq,
        show (∑ i, ‖((WithLp.equiv 2 ((Fin (2 * N + 2) → Fin 2) → ℂ)).symm
              (basisVec (tJConfigOf N (Classical.choice hNE).val))).ofLp i‖ ^ 2) = (1 : ℝ) from ?_]
      · simp
      · rw [Finset.sum_eq_single (tJConfigOf N (Classical.choice hNE).val)]
        · simp
        · intro b _ hb; simp [basisVec_of_ne hb]
        · intro h; exact absurd (Finset.mem_univ _) h
    · exact fermionTotalNumber_mulVec_tJConfigOf_eq N _ Ne (Classical.choice hNE).property
    · exact tJConfigOf_mem_hardcore N _
  unfold groundEnergyAtFilling
  refine le_ciInf (fun φ => le_trans hμE0 ?_)
  obtain ⟨hnorm, hN, hhc⟩ := φ.property
  set c := tJFillingExpansionCoeff N Ne (φ : EuclideanSpace ℂ _).ofLp with hcdef
  have hcompl : (φ : EuclideanSpace ℂ _).ofLp = tJFillingExpansion N Ne c :=
    tJ_filling_completeness Ne _ hhc hN
  have hcc : (dotProduct (star c) c).re = 1 := by
    have hiso := tJFillingExpansion_dotProduct_self Ne c
    rw [← hcompl] at hiso
    rw [← hiso, dotProduct_star_ofLp_self_eq_one hnorm, Complex.one_re]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hHW c
  rw [hcc, mul_one] at hvar
  calc hermitianMinEigenvalue hHW
      ≤ rayleighOnVec (tJFillingCompress N Ne (tJHamiltonian N (cycleGraph (N + 1)) τ J)) c := hvar
    _ = rayleighOnVec (tJHamiltonian N (cycleGraph (N + 1)) τ J)
          (φ : EuclideanSpace ℂ _).ofLp := by
        rw [rayleighOnVec_tJFillingCompress, ← hcompl]

-- Raised heartbeat budget: this E2 capstone chains several heavy facts (the lifted
-- PF eigenvector admissibility and the W-restricted A.17 lower bound) whose combined
-- elaboration exceeds the default limit.
set_option maxHeartbeats 1000000 in
/-- **E2 capstone: `groundEnergyAtFilling = μ`.** The ground energy of the d=1 ferromagnetic t-J
model at odd filling `Ne` equals the Perron–Frobenius sector minimum `μ`: `≤` from the lifted PF
eigenvector being admissible (`tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen`), `≥` from the
W-restricted A.17 (`tJ_groundEnergyAtFilling_ge_of_sectorMin`).  Packaged with the PF eigenvector `v`
(strictly positive) at `μ`, the unique positive spin-charge-separated ground state. -/
theorem tJHamiltonian_groundEnergyAtFilling_eq_perronFrobeniusMin (hpos : 0 < N) (Ne : ℕ)
    (hNeLt : Ne < N + 1) (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) :
    ∃ (μ : ℝ) (v : TJSpinHalfFillingSector N Ne → ℝ), (∀ q, 0 < v q) ∧
      (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ v = μ • v ∧
      groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne = μ := by
  classical
  haveI : Fact (Ne < N + 1) := ⟨hNeLt⟩
  haveI : Fact (Odd Ne) := ⟨hodd⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ q : TJSpinHalfFillingSector N Ne,
      tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q < c :=
    ⟨(Finset.univ.sup' Finset.univ_nonempty
        (fun q => tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q)) + 1,
      fun q => lt_of_le_of_lt
        (Finset.le_sup' (fun q => tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q)
          (Finset.mem_univ q)) (lt_add_one _)⟩
  obtain ⟨μ, v, hvpos, hveig, hmin, _⟩ :=
    tJEffReMatrixOnSector_perronFrobenius hpos Ne hNeLt hodd τ J hτ hJ c hc
  have hv0 : v ≠ 0 := by
    intro h
    have := hvpos (Classical.arbitrary (TJSpinHalfFillingSector N Ne))
    rw [h] at this
    simp at this
  have hle : groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ≤ μ :=
    tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen hpos Ne hodd τ J hτ.le hJ.le hv0 μ hveig
  have hge : μ ≤ groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne :=
    tJ_groundEnergyAtFilling_ge_of_sectorMin hpos Ne hNeLt hodd τ J hτ.le hJ.le hmin
  exact ⟨μ, v, hvpos, hveig, le_antisymm hle hge⟩

end LatticeSystem.Fermion
