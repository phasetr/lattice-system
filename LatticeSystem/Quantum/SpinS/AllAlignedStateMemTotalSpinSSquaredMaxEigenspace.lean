import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace

/-!
# All-aligned states are in the max-Casimir `(Ŝ_tot)²` eigenspace

Both `|σ_⊤⟩ = allAlignedStateS V N 0` and `|σ_⊥⟩ =
allAlignedStateS V N (Fin.last N)` are `(Ŝ_tot)²`-eigenvectors at
the maximum eigenvalue `m_max(m_max+1) =
saturatedFerromagnetCasimirEigenvalueS V N`:

  `|σ_⊤⟩, |σ_⊥⟩ ∈ Module.End.eigenspace (Ŝ_tot)².mulVecLin
                    (saturatedFerromagnetCasimirEigenvalueS V N)`.

Direct from PR #878 / PR #879 (eigenvalue formulas on all-aligned
states) packaged as eigenspace memberships.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- `|σ_⊤⟩ ∈ (Ŝ_tot)² eigenspace at max Casimir`. -/
theorem allAlignedStateS_zero_mem_totalSpinSSquaredEigenspace_max
    [Nonempty V] :
    (allAlignedStateS V N (0 : Fin (N + 1)) :
        (V → Fin (N + 1)) → ℂ) ∈
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  unfold saturatedFerromagnetCasimirEigenvalueS
  exact totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue

set_option linter.style.longLine false in
/-- `|σ_⊥⟩ ∈ (Ŝ_tot)² eigenspace at max Casimir`. -/
theorem allAlignedStateS_last_mem_totalSpinSSquaredEigenspace_max
    [Nonempty V] :
    (allAlignedStateS V N (Fin.last N) :
        (V → Fin (N + 1)) → ℂ) ∈
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  unfold saturatedFerromagnetCasimirEigenvalueS
  exact totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue

end LatticeSystem.Quantum
