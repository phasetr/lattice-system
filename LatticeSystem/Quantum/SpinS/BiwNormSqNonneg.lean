import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `0 ≤ ‖biw‖²` unconditionally

Packaged trivial inequality `0 ≤ ‖biw‖²` via `sq_nonneg`. Useful as
a building block for chained inequalities involving `‖biw‖²`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ ‖biw‖²`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_sq_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 :=
  sq_nonneg _

end LatticeSystem.Quantum
