import LatticeSystem.Math.HermitianEigenspaceBotAboveMax

/-!
# Hermitian max eigenvalue `≥ μ` when an eigenvector at `μ` exists

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.d): For a Hermitian matrix `M` on a non-empty finite-dim complex space, if
`w ≠ 0` satisfies `M w = (μ : ℂ) w` (for some `μ : ℝ`), then
`μ ≤ hermitianMaxEigenvalue M`.

Proof via the contrapositive of (j.13.c) (`hermitian_eigenspace_eq_bot_of_real_gt_max`):
if `hermitianMaxEigenvalue M < μ`, then the eigenspace at `(μ : ℂ)` is `⊥`,
contradicting the existence of `w ≠ 0`.

Mirror of `LatticeSystem.Quantum.hermitian_min_eigenvalue_le_of_eigenvector_exists`
((j.3) #3859, `LatticeSystem/Quantum/SpinS/HermitianMinLeOfEigenvector.lean`) on
the maximum side.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math

open Matrix Module

/-- **Hermitian max eigenvalue `≥ μ` from an eigenvector at `μ`**: contrapositive of
(j.13.c). -/
theorem hermitian_max_eigenvalue_ge_of_eigenvector_exists
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {μ : ℝ} {w : n → ℂ} (hw_ne : w ≠ 0)
    (hw_eig : Matrix.mulVec M w = (μ : ℂ) • w) :
    μ ≤ hermitianMaxEigenvalue hM := by
  by_contra hμ
  push Not at hμ
  -- hμ : hermitianMaxEigenvalue hM < μ
  have h_bot := hermitian_eigenspace_eq_bot_of_real_gt_max hM hμ
  -- w is in the eigenspace at (μ : ℂ).
  have hw_mem : w ∈ End.eigenspace (Matrix.toLin' M) ((μ : ℂ)) := by
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hw_eig
  rw [h_bot, Submodule.mem_bot] at hw_mem
  exact hw_ne hw_mem

end LatticeSystem.Math
