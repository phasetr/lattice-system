import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `0 ≤ biw.re²` unconditionally

Trivial packaging of `sq_nonneg` for `biw.re`. Useful as a reusable
hypothesis when reasoning about biw.re² appearing in closed forms.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ biw.re²`** unconditionally. Packaged `sq_nonneg`. -/
theorem bipartiteImbalanceWeight_re_sq_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := sq_nonneg _

end LatticeSystem.Quantum
