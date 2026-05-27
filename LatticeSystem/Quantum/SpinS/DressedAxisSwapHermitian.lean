import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic

/-!
# Hermiticity of the Marshall-dressed axis-swapped Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For real couplings (`J, λ, D` real) the Marshall-dressed axis-swapped Hamiltonian is Hermitian:
it is the conjugation `Θ_A Ĥ' Θ_A` of the Hermitian `Ĥ'` by the Hermitian (real, `±1`-diagonal)
Marshall sign matrix `Θ_A`.  Together with the off-diagonal non-positivity (#3770) this makes
`−Ĥ'_dressed` a real symmetric matrix with non-negative off-diagonal entries on each parity block
— the symmetric Perron–Frobenius input for the degeneracy bound (PR5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Hermiticity of the dressed axis-swapped Hamiltonian** for real couplings. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_isHermitian_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).IsHermitian := by
  have hHerm := axisSwappedAnisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
    (fun x y => by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hJ x y)
    (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
    (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hD)
  have hdiag : (Matrix.diagonal (marshallSignS A) : ManyBodyOpS Λ N).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_eq_iff_im]
    exact marshallSignS_im A i
  rw [Matrix.IsHermitian, dressedAxisSwappedAnisotropicHeisenbergS_eq_diag_conj,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hdiag.eq, hHerm.eq, mul_assoc]

end LatticeSystem.Quantum
