import LatticeSystem.Quantum.SpinS.BiwNormEqHalfCardIffSaturatedOrZero

/-!
# iff: `2 · ‖biw‖ = |Λ| · N ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

Doubled form of PR #3227.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·‖biw‖ = |Λ|·N iff saturated or N = 0`** unconditionally. Doubled form of PR #3227. -/
theorem two_bipartiteImbalanceWeight_norm_eq_card_times_n_iff_saturated_or_n_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = (Fintype.card Λ : ℝ) * (N : ℝ) ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  have hiff := bipartiteImbalanceWeight_norm_eq_half_card_iff_saturated_or_n_zero
    (Λ := Λ) A N
  constructor
  · intro heq
    exact hiff.mp (by linarith)
  · intro hor
    have := hiff.mpr hor
    linarith

end LatticeSystem.Quantum
