import LatticeSystem.Quantum.SpinS.BiwNormLeHalfCard

/-!
# `biw.re ≤ |Λ|·N/2` unconditionally

The real part of the bipartite imbalance weight is bounded above by its
norm, which in turn is bounded above by `|Λ|·N/2` (PR #3232):

  `biw.re ≤ ‖biw‖ ≤ |Λ|·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re ≤ |Λ|·N/2`** unconditionally. -/
theorem bipartiteImbalanceWeight_re_le_half_card
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  classical
  have h_re_le_norm : (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := Complex.re_le_norm _
  have h_norm_le := bipartiteImbalanceWeight_norm_le_half_card (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
