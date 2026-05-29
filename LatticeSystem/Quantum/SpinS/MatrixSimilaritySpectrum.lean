import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Similarity preserves the matrix spectrum

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.7): for similar matrices `M' = Uinv * M * U` with `U * Uinv = 1`, `Uinv * U = 1`, the
spectra `spectrum ℂ M = spectrum ℂ M'` agree. Proved via the existing
`matrix_similar_eigenspace_finrank_eq` (#3746): the eigenspaces have equal finrank, so
in particular both are `⊥` or both nontrivial at any `μ`, hence `HasEigenvalue` agrees,
hence spectrum agrees.

The real-spectrum version follows by `spectrum.algebraMap_mem_iff`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Spectrum equality under matrix similarity** (`ℂ`): if `M' = Uinv * M * U` with
`U * Uinv = 1`, `Uinv * U = 1`, then `spectrum ℂ M = spectrum ℂ M'`. -/
theorem matrix_similar_spectrum_complex_eq
    {U Uinv M M' : Matrix n n ℂ} (hUU : U * Uinv = 1) (hUinvU : Uinv * U = 1)
    (hsim : M' = Uinv * M * U) :
    spectrum ℂ M = spectrum ℂ M' := by
  ext μ
  -- Bridge spectrum ↔ HasEigenvalue via Matrix.spectrum_toLin' + hasEigenvalue_iff_mem_spectrum.
  rw [← Matrix.spectrum_toLin', ← Matrix.spectrum_toLin',
    ← Module.End.hasEigenvalue_iff_mem_spectrum,
    ← Module.End.hasEigenvalue_iff_mem_spectrum]
  -- HasEigenvalue ↔ eigenspace ≠ ⊥; finrank equality (#3746) gives the bridge.
  have hfinrank : finrank ℂ (End.eigenspace (Matrix.toLin' M) μ) =
      finrank ℂ (End.eigenspace (Matrix.toLin' M') μ) :=
    (matrix_similar_eigenspace_finrank_eq hUU hUinvU hsim μ).symm
  -- Convert hfinrank's eigenspace to the genEigenspace form (1).
  -- End.eigenspace is definitionally End.genEigenspace _ 1.
  change End.eigenspace (Matrix.toLin' M) μ ≠ ⊥ ↔
         End.eigenspace (Matrix.toLin' M') μ ≠ ⊥
  constructor
  · intro hM h_M'_eq_bot
    apply hM
    have h_M'_fr_zero : finrank ℂ (End.eigenspace (Matrix.toLin' M') μ) = 0 := by
      rw [h_M'_eq_bot]; exact finrank_bot _ _
    have h_M_fr_zero : finrank ℂ (End.eigenspace (Matrix.toLin' M) μ) = 0 := by
      rw [hfinrank]; exact h_M'_fr_zero
    exact Submodule.finrank_eq_zero.mp h_M_fr_zero
  · intro hM' h_M_eq_bot
    apply hM'
    have h_M_fr_zero : finrank ℂ (End.eigenspace (Matrix.toLin' M) μ) = 0 := by
      rw [h_M_eq_bot]; exact finrank_bot _ _
    have h_M'_fr_zero : finrank ℂ (End.eigenspace (Matrix.toLin' M') μ) = 0 := by
      rw [← hfinrank]; exact h_M_fr_zero
    exact Submodule.finrank_eq_zero.mp h_M'_fr_zero

/-- **Spectrum equality under matrix similarity** (`ℝ`): for real spectra of complex
matrices, similarity preserves `spectrum ℝ`. -/
theorem matrix_similar_spectrum_real_eq
    {U Uinv M M' : Matrix n n ℂ} (hUU : U * Uinv = 1) (hUinvU : Uinv * U = 1)
    (hsim : M' = Uinv * M * U) :
    spectrum ℝ M = spectrum ℝ M' := by
  ext μ
  rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ), ← spectrum.algebraMap_mem_iff ℂ (R := ℝ),
    matrix_similar_spectrum_complex_eq hUU hUinvU hsim]

end LatticeSystem.Quantum
