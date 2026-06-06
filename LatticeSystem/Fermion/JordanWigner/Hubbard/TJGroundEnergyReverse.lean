import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOperatorLift
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge

/-!
# Tasaki 11.5: spin-½ `W`-eigenvalues are sector-matrix eigenvalues (Prop 11.24 PR-E2, `≥` crux)

The crux bridge for the reverse ground-energy bound `μ ≤ groundEnergyAtFilling`: a `Ŝ³ = ½`,
`N̂ = Ne`, hard-core (`W`) eigenvector of `Ĥ_tJ` at a real eigenvalue `E` produces a nonzero **real**
eigenvector of the sector matrix `tJEffReMatrixOnSector` at `E`
(`tJ_spinHalf_W_eigenvector_to_sector`).  Combined with the Perron–Frobenius minimality, this gives
`μ ≤ E` for every such `E` (`tJ_perronFrobenius_min_le_of_spinHalf_W_eigenvalue`).

Such an eigenvector is sector-supported (support restriction), so it equals its sector expansion;
the operator action `Ĥ_tJ` then becomes the (complex) sector matrix acting on the coefficient
vector, which is real on the sector (`tJEffMatrix_sector_im_zero`), and a complex eigenvector of a
real matrix at a real eigenvalue has a nonzero real real/imaginary part
(`matrix_eigenvec_re_of_complex` / `_im_of_complex`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **Spin-½ `W`-eigenvector ⟹ real sector eigenvector.** A nonzero `Ŝ³ = ½`, `N̂ = Ne`, hard-core
eigenvector of `Ĥ_tJ` at a real eigenvalue `E` gives a nonzero real eigenvector of
`tJEffReMatrixOnSector` at `E`. -/
theorem tJ_spinHalf_W_eigenvector_to_sector (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne) (τ J : ℝ)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) {Φ : (Fin (2 * N + 2) → Fin 2) → ℂ} (hΦ0 : Φ ≠ 0)
    (hhc : Φ ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec Φ = (Ne : ℂ) • Φ)
    (hSz : (fermionTotalSpinZ N).mulVec Φ = ((1 / 2 : ℝ) : ℂ) • Φ)
    {E : ℝ}
    (hE : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec Φ = (E : ℂ) • Φ) :
    ∃ w : TJSpinHalfFillingSector N Ne → ℝ, w ≠ 0 ∧
      (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ w = E • w := by
  classical
  -- `Φ` is sector-supported, hence its own sector expansion.
  have hsupp : Φ = tJExpansion N Ne (tJExpansionCoeff N Ne Φ) :=
    tJ_completeness Ne Φ (fun w hw =>
      tJ_mulVec_apply_eq_zero_of_not_sector Ne Φ hhc hN hSz w hw)
  set c := tJExpansionCoeff N Ne Φ with hcdef
  -- The complex sector-matrix column acts as `E` on `c`.
  have hceig : (fun s' => ∑ s, c s *
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
    have hcoeff := congrArg (tJExpansionCoeff N Ne) h2
    rw [tJExpansionCoeff_tJExpansion, tJExpansionCoeff_tJExpansion] at hcoeff
    exact hcoeff.symm
  -- Recast as: the real sector matrix (cast to `ℂ`) has complex eigenvector `c` at `E`.
  have hmap : (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).map (Complex.ofReal) *ᵥ c
      = (E : ℂ) • c := by
    rw [show (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).map (Complex.ofReal) *ᵥ c
        = (fun s' => ∑ s, c s * tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val) from ?_, hceig]
    funext s'
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact Finset.sum_congr rfl (fun s _ => by
      rw [tJEffMatrix_sector_eq_ofReal hpos Ne hodd τ J hτ hJ s' s]; ring)
  -- `c ≠ 0` (else `Φ = tJExpansion 0 = 0`).
  have hc0 : c ≠ 0 := by
    intro h
    apply hΦ0
    rw [hsupp, h]
    unfold tJExpansion
    simp
  -- A nonzero real or imaginary part gives the real eigenvector.
  by_cases hre0 : (fun i => (c i).re) = (0 : TJSpinHalfFillingSector N Ne → ℝ)
  · refine ⟨fun i => (c i).im, ?_, matrix_eigenvec_im_of_complex hmap⟩
    intro him0
    exact hc0 (funext fun s => Complex.ext (congrFun hre0 s) (congrFun him0 s))
  · exact ⟨fun i => (c i).re, hre0, matrix_eigenvec_re_of_complex hmap⟩

/-- **Any spin-½ `W`-eigenvalue is bounded below by the Perron–Frobenius minimum `μ`.** Given the
PF minimality of `μ` over the sector matrix, every `Ŝ³ = ½`, `N̂ = Ne`, hard-core eigenvalue `E` of
`Ĥ_tJ` satisfies `μ ≤ E` (its sector eigenvector, from `tJ_spinHalf_W_eigenvector_to_sector`, feeds
the minimality). -/
theorem tJ_sectorMin_le_of_spinHalf_W_eigenvalue (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne) (τ J : ℝ)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) {μ : ℝ}
    (hμmin : ∀ (lam : ℝ) (w : TJSpinHalfFillingSector N Ne → ℝ), w ≠ 0 →
      (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ w = lam • w → μ ≤ lam)
    {Φ : (Fin (2 * N + 2) → Fin 2) → ℂ} (hΦ0 : Φ ≠ 0)
    (hhc : Φ ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec Φ = (Ne : ℂ) • Φ)
    (hSz : (fermionTotalSpinZ N).mulVec Φ = ((1 / 2 : ℝ) : ℂ) • Φ)
    {E : ℝ}
    (hE : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec Φ = (E : ℂ) • Φ) :
    μ ≤ E := by
  obtain ⟨w, hw0, hwE⟩ :=
    tJ_spinHalf_W_eigenvector_to_sector hpos Ne hodd τ J hτ hJ hΦ0 hhc hN hSz hE
  exact hμmin E w hw0 hwE

end LatticeSystem.Fermion
