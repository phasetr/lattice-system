import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance
import LatticeSystem.Quantum.SpinS.MatrixSimilaritySpectrum
import LatticeSystem.Quantum.SpinS.ParityBlockSubmatrixHermitian
import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic
import LatticeSystem.Quantum.SpinS.BareAxisSwapFullEigInterParityLeOne

/-!
# Marshall similarity at the submatrix level: bare/dressed have equal `hermitianMinEigenvalue`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.8): the Marshall sign diagonal `Θ_A` restricted to `parityConfigS Λ N p` is a
similarity between the bare and dressed submatrices. Combined with (j.6) #3863 +
(j.7) #3864, this gives `hermitianMinEigenvalue bare.submatrix = hermitianMinEigenvalue
dressed.submatrix`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The Marshall diagonal restricted to `parityConfigS Λ N p`. -/
noncomputable def marshallDiagonalOnParity (A : Λ → Bool) (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℂ :=
  Matrix.diagonal (fun σ : parityConfigS Λ N p => marshallSignS A σ.1)

/-- **Marshall diagonal squared on parity is `1`** (entrywise from `marshallSignS² = 1`). -/
theorem marshallDiagonalOnParity_mul_self (A : Λ → Bool) (p : ℕ) :
    marshallDiagonalOnParity (Λ := Λ) (N := N) A p *
      marshallDiagonalOnParity (Λ := Λ) (N := N) A p = 1 := by
  unfold marshallDiagonalOnParity
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : parityConfigS Λ N p =>
        marshallSignS A σ.1 * marshallSignS A σ.1) = (fun _ => (1 : ℂ)) from
      funext fun σ => marshallSignS_sq A σ.1]
  exact Matrix.diagonal_one

/-- **Submatrix-level Marshall conjugation**: `dressed.submatrix = Θ_p * bare.submatrix * Θ_p`. -/
theorem dressedAxisSwapped_submatrix_eq_marshall_conj_bare
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (p : ℕ) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1) =
      marshallDiagonalOnParity (Λ := Λ) (N := N) A p *
        (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1) *
        marshallDiagonalOnParity (Λ := Λ) (N := N) A p := by
  ext σ τ
  simp only [Matrix.submatrix_apply, dressedAxisSwappedAnisotropicHeisenbergS_apply,
    marshallDiagonalOnParity, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- **Bare and dressed submatrix `hermitianMinEigenvalue` agree** via Marshall similarity. -/
theorem bare_dressed_submatrix_hermitianMinEigenvalue_eq
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hDim : D.im = 0) (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hlam hDim p) =
      hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p) := by
  apply hermitianMinEigenvalue_eq_of_spectrum_eq
  -- Via (j.7): dressed = Θ_p * bare * Θ_p ⟹ spectrum bare = spectrum dressed.
  apply matrix_similar_spectrum_real_eq
    (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := N) A p)
    (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := N) A p)
  exact dressedAxisSwapped_submatrix_eq_marshall_conj_bare A J lam D p

end LatticeSystem.Quantum
