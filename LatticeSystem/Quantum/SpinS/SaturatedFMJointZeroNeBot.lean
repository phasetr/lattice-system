import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.TotalSpinSSquaredMaxEigenspaceNeBot

/-!
# Saturated-FM joint eigenspace at J=0 is non-trivial

The saturated-FM joint eigenspace at trivial coupling
`J = (0 : V → V → ℂ)` equals the max-Casimir `(Ŝ_tot)²`-eigenspace
(PR #2801), which is non-trivial (PR #2818). Hence:

  `saturatedFerromagnetJointEigenspace (0 : V → V → ℂ) N ≠ ⊥`.

J-independent? At J=0 the saturated FM constraint reduces to the
single Casimir constraint, so existence reduces to PR #2818. Used
as a building block toward existence statements for general J via
SU(2) invariance.

Tracked as part of Tasaki §2.4 Theorem 2.1 / §2.5 Theorem 2.3
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **Saturated-FM joint eigenspace at J=0 is non-trivial**:
`saturatedFerromagnetJointEigenspace 0 N ≠ ⊥`. -/
theorem saturatedFerromagnetJointEigenspace_zero_ne_bot [Nonempty V] :
    saturatedFerromagnetJointEigenspace (V := V) (0 : V → V → ℂ) N ≠ ⊥ := by
  rw [saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace]
  exact totalSpinSSquaredEigenspace_max_ne_bot

end LatticeSystem.Quantum
