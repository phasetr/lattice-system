import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightEqZeroIff

/-!
# `‖bipartiteImbalanceWeight A N‖ = 0` characterisation

`‖z‖ = 0 ↔ z = 0` in any normed space. Combining with PR #2854's
`bipartiteImbalanceWeight = 0 ↔ |A| = |¬A|` (at `N ≥ 1`):

  `‖bipartiteImbalanceWeight A N‖ = 0 ↔ |A| = |¬A|`   (at `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **`‖bipartiteImbalanceWeight A N‖ = 0 ↔ |A| = |¬A|`** (at
`N ≥ 1`). Direct from `norm_eq_zero` + PR #2854. -/
theorem bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq
    (hN : 1 ≤ N) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [norm_eq_zero]
  exact bipartiteImbalanceWeight_eq_zero_iff_card_eq A hN

end LatticeSystem.Quantum
