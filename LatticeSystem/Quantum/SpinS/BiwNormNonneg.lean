import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `0 ≤ ‖biw‖` packaged unconditionally

Trivial via `norm_nonneg`, packaged for inline use.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ ‖biw‖`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
  norm_nonneg _

end LatticeSystem.Quantum
