import LatticeSystem.Quantum.SpinS.MagSubspaceDistinctLI
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Triple linear independence of non-zero vectors in distinct magnetization sectors

(PR #3901, Issue #3739): three non-zero vectors in three pairwise distinct
magnetization sectors are linearly independent. Direct application of mathlib's
`Module.End.eigenvectors_linearIndependent'` to `totalSpinSOp3` viewed as a
linear endomorphism via `Matrix.toLin'`.

This is the contradiction lever for the SU(2) symmetric `finrank ≤ 1` argument
toward Tasaki §2.5 Theorem 2.4 obligation (2.a): three non-zero vectors in three
pairwise distinct sectors form a 3-LI family, contradicting obligation (1)
`finrank ≤ 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Submodule

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Triple LI from pairwise distinct sectors**: three non-zero vectors in three
pairwise distinct magnetization sectors are linearly independent. -/
theorem linearIndependent_triple_of_magSubspaceS_distinct
    {M₁ M₂ M₃ : ℂ} (h₁₂ : M₁ ≠ M₂) (h₁₃ : M₁ ≠ M₃) (h₂₃ : M₂ ≠ M₃)
    {Φ₁ Φ₂ Φ₃ : (Λ → Fin (N + 1)) → ℂ}
    (h₁_mem : Φ₁ ∈ magSubspaceS Λ N M₁) (hΦ₁_ne : Φ₁ ≠ 0)
    (h₂_mem : Φ₂ ∈ magSubspaceS Λ N M₂) (hΦ₂_ne : Φ₂ ≠ 0)
    (h₃_mem : Φ₃ ∈ magSubspaceS Λ N M₃) (hΦ₃_ne : Φ₃ ≠ 0) :
    LinearIndependent ℂ ![Φ₁, Φ₂, Φ₃] := by
  classical
  -- Set up the linear endomorphism `f = totalSpinSOp3` and indexed eigenvalues / eigenvectors.
  set f : Module.End ℂ ((Λ → Fin (N + 1)) → ℂ) := Matrix.toLin' (totalSpinSOp3 Λ N) with hfdef
  let μ : Fin 3 → ℂ := ![M₁, M₂, M₃]
  let v : Fin 3 → ((Λ → Fin (N + 1)) → ℂ) := ![Φ₁, Φ₂, Φ₃]
  -- μ is injective.
  have hμ_inj : Function.Injective μ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exfalso; apply h₁₂; exact hij)
        | (exfalso; apply h₁₂.symm; exact hij)
        | (exfalso; apply h₁₃; exact hij)
        | (exfalso; apply h₁₃.symm; exact hij)
        | (exfalso; apply h₂₃; exact hij)
        | (exfalso; apply h₂₃.symm; exact hij)
  -- Each v i is an eigenvector of f at μ i.
  have hev : ∀ i, f.HasEigenvector (μ i) (v i) := by
    intro i
    fin_cases i
    · refine ⟨?_, hΦ₁_ne⟩
      rw [End.mem_eigenspace_iff, hfdef, Matrix.toLin'_apply]
      exact (mem_magSubspaceS_iff M₁ Φ₁).mp h₁_mem
    · refine ⟨?_, hΦ₂_ne⟩
      rw [End.mem_eigenspace_iff, hfdef, Matrix.toLin'_apply]
      exact (mem_magSubspaceS_iff M₂ Φ₂).mp h₂_mem
    · refine ⟨?_, hΦ₃_ne⟩
      rw [End.mem_eigenspace_iff, hfdef, Matrix.toLin'_apply]
      exact (mem_magSubspaceS_iff M₃ Φ₃).mp h₃_mem
  -- Apply Module.End.eigenvectors_linearIndependent'.
  exact f.eigenvectors_linearIndependent' μ hμ_inj v hev

end LatticeSystem.Quantum
