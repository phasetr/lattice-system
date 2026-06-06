import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOperatorLift
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorGroundState

/-!
# Tasaki 11.5: the t-J eigenvector lift from the sector PF eigenvector (Prop 11.24 PR-E1d)

The Perron–Frobenius ground eigenvector of the real sector matrix lifts to a genuine
`Ĥ_tJ`-eigenvector at the same eigenvalue. Concretely, if `tJEffReMatrixOnSector ·ᵥ c = μ • c`
(real), then `Ĥ_tJ (tJExpansion c) = μ • tJExpansion c` (`tJHamiltonian_mulVec_tJExpansion_ofReal`).

This is the operator-side counterpart of the Nagaoka
`hubbardEffectiveHamiltonian_mulVec_tasakiExpansion`. Two ingredients:

* `tJHamiltonian_mulVec_tJExpansion` — `Ĥ_tJ` acts on a sector expansion as the (complex) sector
  matrix `M_{s',s} = ⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩ = tJEffMatrix`, via the per-basis-state operator lift
  `tJHamiltonian_mulVec_tJConfigOf` and the identification
  `tJExpansionCoeff (Ĥ_tJ|Φ_s⟩) = tJEffMatrix`;
* `tJEffMatrix_sector_im_zero` — on the `Ŝ³ = ½` sector of the odd-`Ne` cycle the matrix entries are
  real (off-diagonals by `tJEffMatrix_offdiag_nonpos`, the diagonal by Hermiticity), so the real
  eigen-equation of `tJEffReMatrixOnSector` upgrades to the complex one needed for the lift.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- The sector-matrix element `⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩` (the `s'`-coefficient of `Ĥ_tJ|Φ_s⟩`) equals the
effective-matrix entry `tJEffMatrix s' s`. -/
theorem tJExpansionCoeff_tJHamiltonian_eq_tJEffMatrix (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) (Ne : ℕ) (s s' : TJSpinHalfFillingSector N Ne) :
    tJExpansionCoeff N Ne ((tJHamiltonian N G τ J).mulVec (basisVec (tJConfigOf N s.val))) s' =
      tJEffMatrix N G τ J s'.val s.val := by
  unfold tJExpansionCoeff
  exact (tJEffMatrix_apply N G τ J s'.val s.val).symm

/-- The per-basis-state operator lift in raw-sum form with the effective-matrix coefficients:
`Ĥ_tJ|Φ_s⟩ = Σ_{s'} M_{s',s} |Φ_{s'}⟩`. -/
theorem tJHamiltonian_mulVec_tJConfigOf' (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (Ne : ℕ) (s : TJSpinHalfFillingSector N Ne) :
    (tJHamiltonian N G τ J).mulVec (basisVec (tJConfigOf N s.val)) =
      ∑ s' : TJSpinHalfFillingSector N Ne,
        tJEffMatrix N G τ J s'.val s.val • basisVec (tJConfigOf N s'.val) := by
  rw [tJHamiltonian_mulVec_tJConfigOf]
  unfold tJExpansion
  exact Finset.sum_congr rfl
    (fun s' _ => by rw [tJExpansionCoeff_tJHamiltonian_eq_tJEffMatrix])

/-- **`Ĥ_tJ` acts on a sector expansion as the effective matrix.**
`Ĥ_tJ (Σ_s c_s |Φ_s⟩) = Σ_{s'} (Σ_s c_s · M_{s',s}) |Φ_{s'}⟩`, the bridge from the operator to the
finite sector matrix `M = tJEffMatrix`. -/
theorem tJHamiltonian_mulVec_tJExpansion (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (Ne : ℕ) (c : TJSpinHalfFillingSector N Ne → ℂ) :
    (tJHamiltonian N G τ J).mulVec (tJExpansion N Ne c) =
      tJExpansion N Ne (fun s' => ∑ s, c s * tJEffMatrix N G τ J s'.val s.val) := by
  unfold tJExpansion
  rw [Matrix.mulVec_sum]
  rw [show (∑ s, (tJHamiltonian N G τ J).mulVec (c s • basisVec (tJConfigOf N s.val)))
      = ∑ s : TJSpinHalfFillingSector N Ne, ∑ s' : TJSpinHalfFillingSector N Ne,
          (c s * tJEffMatrix N G τ J s'.val s.val) • basisVec (tJConfigOf N s'.val) from by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Matrix.mulVec_smul, tJHamiltonian_mulVec_tJConfigOf', Finset.smul_sum]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [smul_smul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [← Finset.sum_smul]

/-- On the `Ŝ³ = ½` sector of the odd-`Ne` periodic chain, the effective-matrix entries are real:
off-diagonals by `tJEffMatrix_offdiag_nonpos`, the diagonal by Hermiticity. -/
theorem tJEffMatrix_sector_im_zero (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne) (τ J : ℝ)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (s' s : TJSpinHalfFillingSector N Ne) :
    (tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val).im = 0 := by
  rcases eq_or_ne s' s with h | h
  · subst h
    have hH := (tJEffMatrix_isHermitian N (cycleGraph (N + 1)) τ J).apply s'.val s'.val
    rw [Complex.star_def] at hH
    exact Complex.conj_eq_iff_im.mp hH
  · exact (tJEffMatrix_offdiag_nonpos N hpos s.val s'.val Ne s.property.2 hodd τ J hτ hJ
      (fun heq => h (Subtype.ext heq))).2

/-- The complex sector entry equals its real part as a real number cast back to `ℂ`. -/
theorem tJEffMatrix_sector_eq_ofReal (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne) (τ J : ℝ)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (s' s : TJSpinHalfFillingSector N Ne) :
    tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val =
      ((tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J s' s : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [Complex.ofReal_re]; rfl
  · rw [Complex.ofReal_im]
    exact tJEffMatrix_sector_im_zero hpos Ne hodd τ J hτ hJ s' s

/-- **Eigenvector lift.** A real Perron–Frobenius eigenvector `c` of `tJEffReMatrixOnSector` at
eigenvalue `μ` lifts to an `Ĥ_tJ`-eigenvector `tJExpansion c` at the same eigenvalue:
`Ĥ_tJ (tJExpansion c) = μ • tJExpansion c`. -/
theorem tJHamiltonian_mulVec_tJExpansion_ofReal (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne) (τ J : ℝ)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (c : TJSpinHalfFillingSector N Ne → ℝ) (μ : ℝ)
    (hc : (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ c = μ • c) :
    (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec
        (tJExpansion N Ne (fun s => (c s : ℂ))) =
      (μ : ℂ) • tJExpansion N Ne (fun s => (c s : ℂ)) := by
  rw [tJHamiltonian_mulVec_tJExpansion]
  have hcoeff : (fun s' => ∑ s, (c s : ℂ) *
      tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val) =
      fun s' => (μ : ℂ) * (c s' : ℂ) := by
    funext s'
    have hre : ∑ s, c s * tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J s' s = μ * c s' := by
      have := congrFun hc s'
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      exact Finset.sum_congr rfl (fun s _ => mul_comm _ _)
    calc ∑ s, (c s : ℂ) * tJEffMatrix N (cycleGraph (N + 1)) τ J s'.val s.val
        = ∑ s, ((c s * tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J s' s : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [tJEffMatrix_sector_eq_ofReal hpos Ne hodd τ J hτ hJ s' s]
          push_cast; ring
      _ = ((∑ s, c s * tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J s' s : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
      _ = (μ : ℂ) * (c s' : ℂ) := by rw [hre]; push_cast; ring
  rw [hcoeff]
  unfold tJExpansion
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [smul_smul]

end LatticeSystem.Fermion
