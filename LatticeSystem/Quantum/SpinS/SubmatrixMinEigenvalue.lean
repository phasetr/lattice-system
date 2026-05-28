import LatticeSystem.Quantum.SpinS.SubmatrixEigenvalueReal
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Submatrix minimum eigenvalue (Hermitian)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.3): for a parity-`p` submatrix of the bare/dressed axis-swapped Hamiltonian (Hermitian
under real couplings via #3846), the minimum of its eigenvalue function exists when
`parityConfigS Λ N p` is non-empty.  This gives a concrete real number `ν_min` characterized
as the minimum of the Hermitian eigenvalue array — the candidate for "PF eigenvalue = spectrum
minimum" identification.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Hermitian matrix minimum eigenvalue** (generic): for a non-empty Hermitian matrix
`M : Matrix n n ℂ`, the minimum of its eigenvalue function `Matrix.IsHermitian.eigenvalues`,
defined as `Finset.min'` over `Finset.univ.image hM.eigenvalues`. -/
noncomputable def hermitianMinEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : ℝ :=
  ((Finset.univ : Finset n).image hM.eigenvalues).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The minimum eigenvalue is in the image of the eigenvalue function. -/
theorem hermitian_min_eigenvalue_mem_image
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    hermitianMinEigenvalue hM ∈
      (Finset.univ : Finset n).image hM.eigenvalues :=
  Finset.min'_mem _ _

/-- The minimum eigenvalue is `≤` every eigenvalue. -/
theorem hermitian_min_eigenvalue_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    hermitianMinEigenvalue hM ≤ hM.eigenvalues i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- **Bare `Ĥ'` submatrix has a minimum eigenvalue**. -/
noncomputable def axisSwappedAnisotropicHeisenbergS_submatrix_min_eigenvalue
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] : ℝ :=
  hermitianMinEigenvalue
    (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real (Λ := Λ) (N := N)
      hJ hlam hD p)

/-- **Dressed `Ĥ'` submatrix has a minimum eigenvalue**. -/
noncomputable def dressedAxisSwappedAnisotropicHeisenbergS_submatrix_min_eigenvalue
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] : ℝ :=
  hermitianMinEigenvalue
    (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real (Λ := Λ) (N := N)
      A hJ hlam hD p)

end LatticeSystem.Quantum
