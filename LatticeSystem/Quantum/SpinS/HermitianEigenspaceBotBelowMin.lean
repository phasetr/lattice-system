import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Hermitian eigenspace is `⊥` for any value strictly below the minimum eigenvalue

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.4): For a Hermitian matrix `M` on a finite-dim complex space, if `μ < hermitianMinEigenvalue M`,
then the eigenspace at `(μ : ℂ)` is `⊥`.

Combines (i.2) #3847 (realness of Hermitian eigenvalues) and (i.3) #3848 (min eigenvalue
exists) with Mathlib's spectrum-eigenvalues bridge (`spectrum_real_eq_range_eigenvalues`,
`hasEigenvalue_iff_mem_spectrum`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Hermitian eigenspace = `⊥` below the minimum eigenvalue** (generic, on `(μ : ℂ)`).

For a Hermitian matrix `M` on a finite-dim complex space, if `μ < hermitianMinEigenvalue M`,
then the eigenspace at `(μ : ℂ)` is `⊥` (no eigenvectors below the spectrum minimum).

Used by (i.5) (#3850) to bound the full block-diagonal eigenspace below the joint per-block
minimum. -/
theorem hermitian_eigenspace_eq_bot_of_real_lt_min
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {μ : ℝ} (hμ : μ < hermitianMinEigenvalue hM) :
    End.eigenspace (Matrix.toLin' M) (μ : ℂ) = ⊥ := by
  by_contra h_ne
  -- From eig ≠ ⊥: μ is an eigenvalue.
  have h_eigen : End.HasEigenvalue (Matrix.toLin' M) (μ : ℂ) := h_ne
  -- HasEigenvalue ↔ μ ∈ spectrum ℂ (toLin' M).
  have h_spec : (μ : ℂ) ∈ spectrum ℂ (Matrix.toLin' M) :=
    h_eigen.mem_spectrum
  -- spectrum ℂ (toLin' M) = spectrum ℂ M.
  rw [Matrix.spectrum_toLin'] at h_spec
  -- (μ : ℂ) = RCLike.ofReal μ, hence in spectrum ℝ M (by algebraMap_mem_iff).
  have h_real_spec : μ ∈ spectrum ℝ M := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]
    exact h_spec
  -- spectrum ℝ M = range of hM.eigenvalues.
  rw [hM.spectrum_real_eq_range_eigenvalues] at h_real_spec
  obtain ⟨i, hi⟩ := h_real_spec
  -- hM.eigenvalues i = μ, but min ≤ eigenvalues i, contradicting μ < min.
  have hle : hermitianMinEigenvalue hM ≤ hM.eigenvalues i := hermitian_min_eigenvalue_le hM i
  linarith

end LatticeSystem.Quantum
