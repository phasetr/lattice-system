import LatticeSystem.Quantum.SpinS.BiwNormEqAbsRe

/-!
# `biw.re² = ‖biw‖²` unconditionally

Squaring PR #3294 (`‖biw‖ = |biw.re|`) gives `‖biw‖² = |biw.re|² = biw.re²`.
This is the cleanest form for substitution into closed-form identities.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re² = ‖biw‖²`** unconditionally. -/
theorem bipartiteImbalanceWeight_re_sq_eq_norm_sq
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 := by
  rw [bipartiteImbalanceWeight_norm_eq_abs_re, sq_abs]

end LatticeSystem.Quantum
