import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `hermitianMinEigenvalue` similarity invariance

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.6): for similar Hermitian matrices `M' = Uinv * M * U`, the `hermitianMinEigenvalue`
is invariant. Proof: the `ℝ`-spectrum is the same (similarity), and
`spectrum_real_eq_range_eigenvalues` identifies the spectrum with the range of the
eigenvalue function. Thus the `Finset.image hM.eigenvalues Finset.univ` (as a set of real
numbers) is the same, and so is its minimum.

This enables transferring `hermitianMinEigenvalue` bounds (e.g., from (j.5) #3861) between
the dressed and bare submatrices via the Marshall similarity.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Hermitian eigenvalue ranges agree under same `ℝ`-spectrum**: if two Hermitian
matrices have the same `ℝ`-spectrum, their `Finset.image eigenvalues Finset.univ` are equal
as Finsets. -/
private theorem hermitian_eigenvalues_image_eq_of_spectrum_eq
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M M' : Matrix n n ℂ} (hM : M.IsHermitian) (hM' : M'.IsHermitian)
    (hspec : spectrum ℝ M = spectrum ℝ M') :
    (Finset.univ : Finset n).image hM.eigenvalues =
      (Finset.univ : Finset n).image hM'.eigenvalues := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rw [← Set.mem_range, ← Set.mem_range,
      ← hM.spectrum_real_eq_range_eigenvalues,
      ← hM'.spectrum_real_eq_range_eigenvalues, hspec]

/-- **`hermitianMinEigenvalue` agrees on Hermitian matrices with the same `ℝ`-spectrum**. -/
theorem hermitianMinEigenvalue_eq_of_spectrum_eq
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M M' : Matrix n n ℂ} (hM : M.IsHermitian) (hM' : M'.IsHermitian)
    (hspec : spectrum ℝ M = spectrum ℝ M') :
    hermitianMinEigenvalue hM = hermitianMinEigenvalue hM' := by
  unfold hermitianMinEigenvalue
  congr 1
  exact hermitian_eigenvalues_image_eq_of_spectrum_eq hM hM' hspec

end LatticeSystem.Quantum
