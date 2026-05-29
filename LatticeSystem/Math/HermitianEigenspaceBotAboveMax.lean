import LatticeSystem.Math.HermitianMaxEigenvalue
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Hermitian eigenspace is `⊥` for any value strictly above the maximum eigenvalue

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.c): For a Hermitian matrix `M` on a non-empty finite-dim complex space, if
`hermitianMaxEigenvalue M < μ`, then the eigenspace at `(μ : ℂ)` is `⊥`.

Mirror of `LatticeSystem.Quantum.hermitian_eigenspace_eq_bot_of_real_lt_min`
((i.4) #3849, `LatticeSystem/Quantum/SpinS/HermitianEigenspaceBotBelowMin.lean`) on
the maximum side, needed by (j.13.d) for `hermitianMaxEigenvalue ≥ μ` from
eigenvector existence.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math

open Matrix Module

/-- **Hermitian eigenspace = `⊥` above the maximum eigenvalue** (generic, on `(μ : ℂ)`).

For a Hermitian matrix `M` on a non-empty finite-dim complex space, if
`hermitianMaxEigenvalue M < μ`, then the eigenspace at `(μ : ℂ)` is `⊥` (no
eigenvectors above the spectrum maximum).

Mirror of (i.4) `hermitian_eigenspace_eq_bot_of_real_lt_min` (#3849). -/
theorem hermitian_eigenspace_eq_bot_of_real_gt_max
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {μ : ℝ} (hμ : hermitianMaxEigenvalue hM < μ) :
    End.eigenspace (Matrix.toLin' M) (μ : ℂ) = ⊥ := by
  by_contra h_ne
  have h_eigen : End.HasEigenvalue (Matrix.toLin' M) (μ : ℂ) := h_ne
  have h_spec : (μ : ℂ) ∈ spectrum ℂ (Matrix.toLin' M) :=
    h_eigen.mem_spectrum
  rw [Matrix.spectrum_toLin'] at h_spec
  have h_real_spec : μ ∈ spectrum ℝ M := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]
    exact h_spec
  rw [hM.spectrum_real_eq_range_eigenvalues] at h_real_spec
  obtain ⟨i, hi⟩ := h_real_spec
  have hle : hM.eigenvalues i ≤ hermitianMaxEigenvalue hM := hermitian_eigenvalue_le_max hM i
  linarith

end LatticeSystem.Math
