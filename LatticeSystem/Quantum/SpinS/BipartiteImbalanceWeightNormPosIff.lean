import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqZero

/-!
# Iff: `‖biw‖ > 0 ↔ unbalanced` at `N ≥ 1`

PR #2855: `‖biw‖ = 0 ↔ balanced` at `N ≥ 1`.

Taking contrapositive (using `‖biw‖ ≥ 0` unconditionally):
`‖biw‖ > 0 ↔ ‖biw‖ ≠ 0 ↔ ¬ balanced ↔ unbalanced`.

  `‖biw‖ > 0 ↔ |A| ≠ |¬A|`   at `N ≥ 1`.

Iff form of PR #2867 (forward direction) + PR #2855 (backward).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff: `‖biw‖ > 0 ↔ unbalanced`** at `N ≥ 1`. -/
theorem bipartiteImbalanceWeight_norm_pos_iff_card_ne
    (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) :
    0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [show (0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) ↔
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≠ 0 from
        ⟨ne_of_gt, fun h => lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)⟩,
      ne_eq,
      bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq A hN]

end LatticeSystem.Quantum
