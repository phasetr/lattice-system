import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian maximum eigenvalue

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.b): For a non-empty Hermitian matrix `M : Matrix n n ℂ`, define
`hermitianMaxEigenvalue hM : ℝ` as the maximum of the eigenvalue function
`Matrix.IsHermitian.eigenvalues` (via `Finset.max'`).

Mirror of `LatticeSystem.Quantum.hermitianMinEigenvalue`
(LatticeSystem/Quantum/SpinS/SubmatrixMinEigenvalue.lean) for the maximum side
needed by the Collatz-Wielandt characterization.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math

open Matrix

/-- **Hermitian matrix maximum eigenvalue** (generic): for a non-empty Hermitian matrix
`M : Matrix n n ℂ`, the maximum of its eigenvalue function `Matrix.IsHermitian.eigenvalues`,
defined as `Finset.max'` over `Finset.univ.image hM.eigenvalues`. -/
noncomputable def hermitianMaxEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : ℝ :=
  ((Finset.univ : Finset n).image hM.eigenvalues).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The maximum eigenvalue is in the image of the eigenvalue function. -/
theorem hermitian_max_eigenvalue_mem_image
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    hermitianMaxEigenvalue hM ∈
      (Finset.univ : Finset n).image hM.eigenvalues :=
  Finset.max'_mem _ _

/-- Every eigenvalue is `≤` the maximum eigenvalue. -/
theorem hermitian_eigenvalue_le_max
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    hM.eigenvalues i ≤ hermitianMaxEigenvalue hM :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

end LatticeSystem.Math
