import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.AllAlignedStateMemTotalSpinSSquaredMaxEigenspace

/-!
# `|σ_⊥⟩` is an explicit witness of `saturatedFerromagnetJointEigenspace 0 N`

All-down mirror of PR #2846 (`|σ_⊤⟩` witness). The all-down state
`allAlignedStateS V N (Fin.last N)` sits in the max-Casimir
`(Ŝ_tot)²` eigenspace just like `|σ_⊤⟩` does, hence in the
saturated-FM joint eigenspace at trivial coupling.

Tracked as part of Tasaki §2.4 Theorem 2.1 / §2.5 Theorem 2.3
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **`|σ_⊥⟩` is an explicit witness of the saturated-FM joint
eigenspace at trivial coupling**:
`allAlignedStateS V N (Fin.last N) ∈ saturatedFerromagnetJointEigenspace (0 : V → V → ℂ) N`. -/
theorem allAlignedStateS_last_mem_saturatedFerromagnetJointEigenspace_zero
    [Nonempty V] :
    (allAlignedStateS V N (Fin.last N) :
        (V → Fin (N + 1)) → ℂ) ∈
      saturatedFerromagnetJointEigenspace (V := V) (0 : V → V → ℂ) N := by
  rw [saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace]
  exact allAlignedStateS_last_mem_totalSpinSSquaredEigenspace_max

end LatticeSystem.Quantum
