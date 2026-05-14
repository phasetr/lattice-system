import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.AllAlignedStateMemTotalSpinSSquaredMaxEigenspace

/-!
# `|σ_⊤⟩` is an explicit witness of `saturatedFerromagnetJointEigenspace 0 N`

PR #2821 establishes
`saturatedFerromagnetJointEigenspace (0 : V → V → ℂ) N ≠ ⊥` by
collapsing to the max-Casimir eigenspace (PR #2801) which contains
`|σ_⊤⟩` (PR #2814).

This file pins down the explicit witness:

  `allAlignedStateS V N 0 ∈ saturatedFerromagnetJointEigenspace 0 N`.

Tracked as part of Tasaki §2.4 Theorem 2.1 / §2.5 Theorem 2.3
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **`|σ_⊤⟩` is an explicit witness of the saturated-FM joint
eigenspace at trivial coupling**:
`allAlignedStateS V N 0 ∈ saturatedFerromagnetJointEigenspace (0 : V → V → ℂ) N`. -/
theorem allAlignedStateS_zero_mem_saturatedFerromagnetJointEigenspace_zero
    [Nonempty V] :
    (allAlignedStateS V N (0 : Fin (N + 1)) :
        (V → Fin (N + 1)) → ℂ) ∈
      saturatedFerromagnetJointEigenspace (V := V) (0 : V → V → ℂ) N := by
  rw [saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace]
  exact allAlignedStateS_zero_mem_totalSpinSSquaredEigenspace_max

end LatticeSystem.Quantum
