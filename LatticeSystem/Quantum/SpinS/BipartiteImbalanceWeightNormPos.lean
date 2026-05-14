import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqZero

/-!
# Strict positivity of `‖bipartiteImbalanceWeight A N‖`

When `|A| ≠ |¬A|` and `N ≥ 1`, the imbalance-weight norm is
strictly positive:

  `0 < ‖bipartiteImbalanceWeight A N‖`.

Contrapositive of PR #2855
(`bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **Strict positivity of `‖bipartiteImbalanceWeight A N‖`** when
`|A| ≠ |¬A|` and `N ≥ 1`. Contrapositive of PR #2855. -/
theorem bipartiteImbalanceWeight_norm_pos_of_card_ne
    (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [norm_pos_iff]
  intro hzero
  have := (bipartiteImbalanceWeight_eq_zero_iff_card_eq A hN).mp hzero
  exact h this

end LatticeSystem.Quantum
