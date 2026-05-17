import LatticeSystem.Quantum.SpinS.BiwNormLeHalfCard
import LatticeSystem.Quantum.SpinS.BiwNormEqHalfCardIffSaturatedOrZero

/-!
# iff: `‖biw‖ < |Λ|·N/2 ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`

Strict companion of PR #3227 (`‖biw‖ = |Λ|·N/2 ↔ saturated or N = 0`).
The biw norm is strictly less than its upper bound exactly at
non-degenerate.

  `‖biw‖ < |Λ|·N/2 ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Combines PR #3226 (`‖biw‖ ≤ |Λ|·N/2`) + PR #3227 (equality iff).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖ < |Λ|·N/2 iff nondeg`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_lt_half_card_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ < (Fintype.card Λ : ℝ) * (N : ℝ) / 2 ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  have hle := bipartiteImbalanceWeight_norm_le_half_card (Λ := Λ) A N
  have heq_iff := bipartiteImbalanceWeight_norm_eq_half_card_iff_saturated_or_n_zero
    (Λ := Λ) A N
  constructor
  · intro hlt
    -- ‖biw‖ < bound → not (‖biw‖ = bound) → not (saturated or N=0) → nondeg.
    have hne : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≠
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := ne_of_lt hlt
    have hnot_sat : ¬ ((Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨ N = 0) :=
      fun h => hne (heq_iff.mpr h)
    push Not at hnot_sat
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.pos_of_ne_zero hnot_sat.1
    · exact Nat.pos_of_ne_zero hnot_sat.2.1
    · exact Nat.pos_of_ne_zero hnot_sat.2.2
  · intro ⟨hA, hNotA, hN⟩
    -- nondeg → not saturated → not (‖biw‖ = bound) → ‖biw‖ < bound (from ≤ side).
    have hnot_sat : ¬ ((Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨ N = 0) := by
      intro hor
      rcases hor with hA0 | hNotA0 | hN0
      · exact absurd hA (by rw [hA0]; exact lt_irrefl _)
      · exact absurd hNotA (by rw [hNotA0]; exact lt_irrefl _)
      · exact absurd hN (by rw [hN0]; exact lt_irrefl _)
    have hne : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≠
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 :=
      fun heq => hnot_sat (heq_iff.mp heq)
    exact lt_of_le_of_ne hle hne

end LatticeSystem.Quantum
