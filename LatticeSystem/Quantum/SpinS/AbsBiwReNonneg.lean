import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `0 ≤ |biw.re|` unconditionally

Trivial packaging of `abs_nonneg` for biw.re.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ |biw.re|`** unconditionally. Packaged `abs_nonneg`. -/
theorem bipartiteImbalanceWeight_abs_re_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := abs_nonneg _

end LatticeSystem.Quantum
