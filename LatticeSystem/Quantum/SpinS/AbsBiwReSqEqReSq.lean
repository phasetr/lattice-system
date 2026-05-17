import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `|biw.re|² = biw.re²` unconditionally

Direct `sq_abs` packaged for the bipartite imbalance weight's real part.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`|biw.re|² = biw.re²`** unconditionally. -/
theorem bipartiteImbalanceWeight_abs_re_sq_eq_re_sq
    (A : Λ → Bool) (N : ℕ) :
    |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ^ 2 =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := sq_abs _

end LatticeSystem.Quantum
