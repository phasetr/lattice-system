import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `‖biw‖ = |biw.re|` unconditionally

The bipartite imbalance weight is purely real, so its norm coincides
with the absolute value of its real part:

  `‖bipartiteImbalanceWeight A N‖ = |(bipartiteImbalanceWeight A N).re|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖ = |biw.re|`** unconditionally. The imbalance weight is real. -/
theorem bipartiteImbalanceWeight_norm_eq_abs_re
    (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
  have him := bipartiteImbalanceWeight_im_zero (Λ := Λ) A N
  rw [Complex.norm_eq_sqrt_sq_add_sq, him]
  simp [Real.sqrt_sq_eq_abs]

end LatticeSystem.Quantum
