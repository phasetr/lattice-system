import LatticeSystem.Quantum.SpinS.BiwNormEqAbsRe

/-!
# `|biw.re| = ‖biw‖` unconditionally

Symmetric form of PR #3294.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`|biw.re| = ‖biw‖`** unconditionally. Symmetric form of PR #3294. -/
theorem bipartiteImbalanceWeight_abs_re_eq_norm
    (A : Λ → Bool) (N : ℕ) :
    |(bipartiteImbalanceWeight (Λ := Λ) A N).re| =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
  (bipartiteImbalanceWeight_norm_eq_abs_re (Λ := Λ) A N).symm

end LatticeSystem.Quantum
