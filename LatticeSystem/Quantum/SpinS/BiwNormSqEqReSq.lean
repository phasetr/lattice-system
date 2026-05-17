import LatticeSystem.Quantum.SpinS.BiwReSqEqNormSq

/-!
# `‖biw‖² = biw.re²` unconditionally

Symmetric form of PR #3324.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖² = biw.re²`** unconditionally. Symmetric form of PR #3324. -/
theorem bipartiteImbalanceWeight_norm_sq_eq_re_sq
    (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 :=
  (bipartiteImbalanceWeight_re_sq_eq_norm_sq (Λ := Λ) A N).symm

end LatticeSystem.Quantum
