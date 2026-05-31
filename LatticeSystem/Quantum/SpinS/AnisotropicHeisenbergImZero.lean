import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergOffDiag
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuity

/-!
# Real entries of the (un-swapped) anisotropic Heisenberg Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Under real coefficients (`(J x y).im = 0`, `lam.im = 0`, `D.im = 0`) every entry
of `anisotropicHeisenbergS J lam D N` — and hence of its magnetisation-sector
restriction `anisotropicHeisenbergS_magSector_submatrix` — has imaginary part
zero.  This is the realness input required by the balanced-magnetisation-sector
Perron–Frobenius route for Theorem 2.4: it turns the complex sector submatrix
into the `(↑) ∘ .re` lift of a real matrix, which is the object the Marshall
similarity / Collatz–Wielandt machinery acts on.

The diagonal case closes from Hermiticity alone (the diagonal of a Hermitian
complex matrix is real); the off-diagonal case reuses the Layer-1 off-diagonal
agreement `anisotropicHeisenbergS_apply_offdiag_eq_heisenberg` together with the
isotropic realness `heisenbergHamiltonianS_apply_im_zero`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Anisotropic Heisenberg entries are real under real coefficients**: every
entry of `anisotropicHeisenbergS J lam D N` has imaginary part zero when `J`,
`lam`, and `D` are real. -/
theorem anisotropicHeisenbergS_apply_im_zero
    {J : Λ → Λ → ℂ} (hJim : ∀ x y, (J x y).im = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0)
    (σ τ : Λ → Fin (N + 1)) :
    (anisotropicHeisenbergS (Λ := Λ) J lam D N σ τ).im = 0 := by
  by_cases hστ : σ = τ
  · -- Diagonal: a Hermitian complex matrix has real diagonal entries.
    subst hστ
    have hH := anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
      (J := J) (lam := lam) (D := D)
      (fun x y => by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hJim x y)
      (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
      (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hDim)
    have hi := hH.apply σ σ
    rw [Complex.star_def, Complex.conj_eq_iff_im] at hi
    exact hi
  · -- Off-diagonal: agrees with the isotropic Heisenberg entry (Layer 1), which
    -- is real for real coupling.
    rw [anisotropicHeisenbergS_apply_offdiag_eq_heisenberg J lam D hστ]
    exact heisenbergHamiltonianS_apply_im_zero N hJim σ τ

/-- **Sector-restricted anisotropic Heisenberg entries are real**: the
magnetisation-`M` submatrix `anisotropicHeisenbergS_magSector_submatrix` has
imaginary part zero entrywise under real coefficients. -/
theorem anisotropicHeisenbergS_magSector_submatrix_im_zero
    {J : Λ → Λ → ℂ} (hJim : ∀ x y, (J x y).im = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0) (M : ℕ)
    (σ τ : magConfigS Λ N M) :
    (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M σ τ).im = 0 := by
  rw [anisotropicHeisenbergS_magSector_submatrix, Matrix.submatrix_apply]
  exact anisotropicHeisenbergS_apply_im_zero hJim hlam hDim σ.1 τ.1

end LatticeSystem.Quantum
