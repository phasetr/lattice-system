import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveNormFoundation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHamiltonianHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHermitianGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveEnergyReconcile
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianVariationalEquality
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariational

/-!
# A positive-semidefinite-`W` ground state (Tasaki §10.2.4)

Layer PR38c toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. This is
the SRP variational step: **the ground energy is attained by a state whose
reconciliation coefficient `W = blockWCoeff` is positive semidefinite.**

Starting from a unit minimum-eigenvector of the Hermitian `Ĥ` (eigenvalue
`μ = hermitianMinEigenvalue`), the Hermitian-`W` representative `φ` (PR37) has
`blockWCoeff φ = W` Hermitian with `Ĥφ = μφ`. The state `φ' := Γ(|W|)` realizing the
spectral absolute value satisfies, by the energy reconciliation (PR33d), the SRP
monotonicity `liebSRPEnergy_abs_le`, and the isometry (PR38a):

  `μ‖φ'‖² ≤ ⟨φ'|Ĥ|φ'⟩ = E(|W|) ≤ E(W) = ⟨φ|Ĥ|φ⟩ = μ‖φ‖² = μ‖φ'‖²`,

so all inequalities are equalities; the Rayleigh-Ritz equality
(`mulVec_eq_smul_of_rayleighOnVec_eq_min`) makes `φ'` a ground vector. As `‖φ'‖ = ‖φ‖ > 0`
it is nonzero, and `blockWCoeff φ' = |W|` is PSD.

## Main result

* `exists_posSemidefW_ground` — a nonzero ground vector with PSD `blockWCoeff`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- **A positive-semidefinite-`W` ground state.** For symmetric real hopping `T` and
nonnegative attraction `U`, there is a nonzero ground vector `φ'` of `Ĥ` (at the minimum
eigenvalue `μ`) whose reconciliation coefficient `blockWCoeff φ'` is positive
semidefinite. -/
theorem exists_posSemidefW_ground
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) (hU : ∀ x, 0 ≤ U x) :
    ∃ φ' : (Fin (2 * N + 2) → Fin 2) → ℂ, φ' ≠ 0 ∧ (blockWCoeff N φ').PosSemidef
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ'
          = ((hermitianMinEigenvalue
              (attractiveHubbardHamiltonian_isHermitian T U hT) : ℝ) : ℂ) • φ' := by
  set hH := attractiveHubbardHamiltonian_isHermitian T U hT with hHdef
  set μ := hermitianMinEigenvalue hH with hμdef
  -- A unit minimum-eigenvector.
  obtain ⟨ψ₀, hψ₀unit, hψ₀eig⟩ := exists_unit_eigenvector_hermitianMinEigenvalue hH
  have hψ₀0 : ψ₀ ≠ 0 := by
    intro h; rw [h] at hψ₀unit; simp [dotProduct] at hψ₀unit
  -- The Hermitian-`W` ground representative (PR37).
  obtain ⟨φ, hφ0, hφHerm, hφeig⟩ := exists_hermitianW_ground T U ψ₀ μ hψ₀0 hψ₀eig
  set φ' := gammaWState N (hermitianAbs hφHerm) with hφ'def
  -- `blockWCoeff φ' = |W|`.
  have hbwφ' : blockWCoeff N φ' = hermitianAbs hφHerm := by
    rw [hφ'def, blockWCoeff, blockWCoeff_gammaWState]
  have hφ'Herm : (blockWCoeff N φ').IsHermitian := by
    rw [hbwφ']; exact hermitianAbs_isHermitian hφHerm
  -- Norm equality `⟨φ',φ'⟩ = ⟨φ,φ⟩`.
  have hnormC : dotProduct (star φ') φ' = dotProduct (star φ) φ := by
    rw [hφ'def, gammaWState_dotProduct_eq, hermitianAbs_sum_normSq_eq,
      ← blockWCoeff_dotProduct_eq]
  -- Rayleigh quotients via the reconciliation.
  have hrayφ : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ
      = liebSRPEnergy (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))
          (fun x => hubbardUpOccupationDiag N x) (fun x => U x / 2) (blockWCoeff N φ) :=
    attractiveHubbardHamiltonian_energy_re_eq_liebSRPEnergy_of_blockW_isHermitian T U hT φ hφHerm
  have hrayφ' : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
      = liebSRPEnergy (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))
          (fun x => hubbardUpOccupationDiag N x) (fun x => U x / 2) (blockWCoeff N φ') :=
    attractiveHubbardHamiltonian_energy_re_eq_liebSRPEnergy_of_blockW_isHermitian T U hT φ' hφ'Herm
  -- SRP monotonicity: `E(|W|) ≤ E(W)`.
  have habs : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
      ≤ rayleighOnVec (attractiveHubbardHamiltonian N T U) φ := by
    rw [hrayφ', hrayφ, hbwφ']
    exact liebSRPEnergy_abs_le hφHerm _ (fun x => hubbardUpOccupationDiag_isHermitian x)
      _ (fun x => by have := hU x; linarith)
  -- `⟨φ|Ĥ|φ⟩ = μ‖φ‖²`.
  have hrayφ_eq : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ
      = μ * (dotProduct (star φ) φ).re := by
    rw [rayleighOnVec, hφeig, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  -- Variational lower bound at `φ'`.
  have hlb : μ * (dotProduct (star φ') φ').re
      ≤ rayleighOnVec (attractiveHubbardHamiltonian N T U) φ' :=
    hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hH φ'
  -- Squeeze ⟹ equality.
  have hsqueeze : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
      = μ * (dotProduct (star φ') φ').re := by
    refine le_antisymm ?_ hlb
    calc rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
        ≤ rayleighOnVec (attractiveHubbardHamiltonian N T U) φ := habs
      _ = μ * (dotProduct (star φ) φ).re := hrayφ_eq
      _ = μ * (dotProduct (star φ') φ').re := by rw [hnormC]
  -- Assemble.
  have hpos : 0 < (dotProduct (star φ') φ').re := by
    rw [hnormC]; exact dotProduct_star_self_re_pos hφ0
  refine ⟨φ', ?_, ?_, ?_⟩
  · intro h; rw [h] at hpos; simp [dotProduct] at hpos
  · rw [hbwφ']; exact hermitianAbs_posSemidef hφHerm
  · exact mulVec_eq_smul_of_rayleighOnVec_eq_min hH hsqueeze

end LatticeSystem.Fermion
