import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Anisotropic Hamiltonian matrix entries vanish across magnetization sectors

(PR #3898, Issue #3739): the matrix entry `anisotropicHeisenbergS J λ D N σ τ`
is `0` whenever `magSumS σ ≠ magSumS τ`. This is the matrix-element form of the
U(1) invariance `[H, Ŝ³_tot] = 0`: H couples only configurations with the same
`Ŝ³_tot` eigenvalue, equivalently with the same `magSumS`.

This is a key technical lemma for the eventual sector-decomposition argument
toward Theorem 2.4 obligation (2.a). With this matrix-element vanishing, the
projection of any H-eigenvector onto a magnetization sector is also an
H-eigenvector at the same eigenvalue, enabling sector-by-sector spectral
analysis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector-crossing matrix entries vanish (U(1) invariance, matrix form)**: for
the anisotropic Heisenberg Hamiltonian, `H σ τ = 0` whenever `magSumS σ ≠
magSumS τ`. This is the matrix-element companion to the U(1) commutation
`[H, Ŝ³_tot] = 0` (#3741). -/
theorem anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne
    (J : Λ → Λ → ℂ) (lam D : ℂ) {σ τ : Λ → Fin (N + 1)}
    (hne : magSumS σ ≠ magSumS τ) :
    anisotropicHeisenbergS J lam D N σ τ = 0 := by
  classical
  -- Commutation as a matrix equation.
  have hcomm : anisotropicHeisenbergS J lam D N * totalSpinSOp3 Λ N =
      totalSpinSOp3 Λ N * anisotropicHeisenbergS J lam D N :=
    (anisotropicHeisenbergS_commute_totalSpinSOp3 J lam D N).eq
  have hentry :
      (anisotropicHeisenbergS J lam D N * totalSpinSOp3 Λ N) σ τ =
      (totalSpinSOp3 Λ N * anisotropicHeisenbergS J lam D N) σ τ := by
    rw [hcomm]
  -- LHS: only ρ = τ contributes (S3 is diagonal).
  have hLHS : (anisotropicHeisenbergS J lam D N * totalSpinSOp3 Λ N) σ τ =
      anisotropicHeisenbergS J lam D N σ τ * magEigenvalueS τ := by
    rw [Matrix.mul_apply]
    rw [Fintype.sum_eq_single τ (fun ρ hρ => by
      rw [totalSpinSOp3_apply_off_diag hρ, mul_zero])]
    rw [totalSpinSOp3_apply_diag]
  -- RHS: only ρ = σ contributes.
  have hRHS : (totalSpinSOp3 Λ N * anisotropicHeisenbergS J lam D N) σ τ =
      magEigenvalueS σ * anisotropicHeisenbergS J lam D N σ τ := by
    rw [Matrix.mul_apply]
    rw [Fintype.sum_eq_single σ (fun ρ hρ => by
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hρ), zero_mul])]
    rw [totalSpinSOp3_apply_diag]
  -- Combine: H σ τ * mE τ = mE σ * H σ τ.
  rw [hLHS, hRHS] at hentry
  -- magSumS σ ≠ magSumS τ ⟹ magEigenvalueS σ ≠ magEigenvalueS τ.
  have hME_ne : magEigenvalueS σ ≠ magEigenvalueS τ := by
    intro heq
    apply hne
    have hsub : (magSumS σ : ℂ) = (magSumS τ : ℂ) := by
      unfold magEigenvalueS at heq
      linear_combination -heq
    exact_mod_cast hsub
  have hdiff_ne : magEigenvalueS τ - magEigenvalueS σ ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm hME_ne)
  -- H σ τ * (mE τ - mE σ) = 0 from hentry.
  have hmul : anisotropicHeisenbergS J lam D N σ τ *
      (magEigenvalueS τ - magEigenvalueS σ) = 0 := by
    linear_combination hentry
  exact (mul_eq_zero.mp hmul).resolve_right hdiff_ne

end LatticeSystem.Quantum
