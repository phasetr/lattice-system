import LatticeSystem.Quantum.SpinS.HermitianEigenspaceBotBelowMin

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Hermitian min eigenvalue `≤ μ` when an eigenvector at `μ` exists

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.3): for a Hermitian matrix `M` on a non-empty finite-dim complex space, if `w ≠ 0`
satisfies `M w = (μ : ℂ) w` (for some `μ : ℝ`), then `hermitianMinEigenvalue M ≤ μ`.

Proof via the contrapositive of (i.4) #3849: if `μ < hermitianMinEigenvalue M`, then
the eigenspace at `(μ : ℂ)` is `⊥`, contradicting the existence of `w ≠ 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Hermitian min eigenvalue `≤ μ` from an eigenvector at `μ`**: contrapositive of (i.4)
#3849. -/
theorem hermitian_min_eigenvalue_le_of_eigenvector_exists
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {μ : ℝ} {w : n → ℂ} (hw_ne : w ≠ 0)
    (hw_eig : Matrix.mulVec M w = (μ : ℂ) • w) :
    hermitianMinEigenvalue hM ≤ μ := by
  by_contra hμ
  push Not at hμ
  -- hμ : μ < hermitianMinEigenvalue hM
  have h_bot := hermitian_eigenspace_eq_bot_of_real_lt_min hM hμ
  -- w is in the eigenspace at (μ : ℂ).
  have hw_mem : w ∈ End.eigenspace (Matrix.toLin' M) ((μ : ℂ)) := by
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hw_eig
  rw [h_bot, Submodule.mem_bot] at hw_mem
  exact hw_ne hw_mem

end LatticeSystem.Quantum
