import LatticeSystem.Quantum.SpinS.ParityBlockSubmatrixHermitian
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Submatrix eigenvalue realness (Hermitian)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.2): the parity-`p` submatrix of the dressed/bare axis-swapped Hamiltonian (Hermitian
under real couplings via #3846) has all eigenvalues real (`μ.im = 0`). Combines #3846
with the existing `isHermitian_eigenvalue_star_eq` (which gives `star μ = μ`, equivalent
to `μ.im = 0` via `Complex.conj_eq_iff_im`).

This is the second step toward the unconditional ground-state degeneracy ≤ 2: the per-sector
PF eigenvalue from (g.2) #3834 is one such Hermitian eigenvalue, and is automatically real.
Combined with Hermitian spectral minimization, it gives min(ν_0, ν_1) as the GS energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Hermitian-submatrix eigenvalues are real** (generic): if `M` is Hermitian and has a
non-trivial eigenspace at `μ`, then `μ.im = 0`. -/
theorem hermitian_eigenvalue_im_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {μ : ℂ} (hμ : End.eigenspace (Matrix.toLin' M) μ ≠ ⊥) :
    μ.im = 0 := by
  -- Extract a non-zero eigenvector.
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  rw [End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv_mem
  -- Apply the existing isHermitian_eigenvalue_star_eq.
  have hstar := isHermitian_eigenvalue_star_eq hM hv_mem hv_ne
  -- star μ = μ ⟹ μ.im = 0.
  rw [Complex.star_def, Complex.conj_eq_iff_im] at hstar
  exact hstar

/-- **Bare `Ĥ'` submatrix eigenvalue is real** for real couplings. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_eigenvalue_im_zero
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ)
    {μ : ℂ}
    (hμ : End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) μ ≠ ⊥) :
    μ.im = 0 :=
  hermitian_eigenvalue_im_zero
    (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real hJ hlam hD p) hμ

/-- **Dressed `Ĥ'` submatrix eigenvalue is real** for real couplings. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_eigenvalue_im_zero
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ)
    {μ : ℂ}
    (hμ : End.eigenspace (Matrix.toLin'
      ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) μ ≠ ⊥) :
    μ.im = 0 :=
  hermitian_eigenvalue_im_zero
    (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real A hJ hlam hD p) hμ

end LatticeSystem.Quantum
