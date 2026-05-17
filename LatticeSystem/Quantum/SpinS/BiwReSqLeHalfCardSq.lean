import LatticeSystem.Quantum.SpinS.BiwNormEqAbsRe
import LatticeSystem.Quantum.SpinS.BiwNormSqLeHalfCardSq

/-!
# `biw.re² ≤ (|Λ|·N/2)²` unconditionally

Real-axis variant of PR #3232 (`‖biw‖² ≤ (|Λ|·N/2)²`) via PR #3294
(`‖biw‖ = |biw.re|`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re² ≤ (|Λ|·N/2)²`** unconditionally. -/
theorem bipartiteImbalanceWeight_re_sq_le_half_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  classical
  have h_norm := bipartiteImbalanceWeight_norm_sq_le_half_card_sq (Λ := Λ) A N
  have h_eq := bipartiteImbalanceWeight_norm_eq_abs_re (Λ := Λ) (A := A) (N := N)
  rw [h_eq, sq_abs] at h_norm
  exact h_norm

end LatticeSystem.Quantum
