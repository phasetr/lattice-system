import LatticeSystem.Quantum.SpinS.BiwNormLtHalfCardIffNondeg

/-!
# iff: `2 · ‖biw‖ < |Λ| · N ↔ nondeg`

Doubled form of PR #3228 (`‖biw‖ < |Λ|·N/2 ↔ nondeg`):

  `2 · ‖biw‖ < |Λ| · N ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·‖biw‖ < |Λ|·N iff nondeg`** unconditionally. Doubled form of PR #3228. -/
theorem two_bipartiteImbalanceWeight_norm_lt_card_times_n_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ < (Fintype.card Λ : ℝ) * (N : ℝ) ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  have hiff := bipartiteImbalanceWeight_norm_lt_half_card_iff_nondeg (Λ := Λ) A N
  constructor
  · intro hlt
    exact hiff.mp (by linarith)
  · intro hor
    have := hiff.mpr hor
    linarith

end LatticeSystem.Quantum
