import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Cardinality at saturated bipartition edges

At the saturated edges (one sublattice empty), the non-empty
sublattice's cardinality equals `|Λ|`:

  `|¬A| = 0 → |A| = |Λ|`,
  `|A| = 0 → |¬A| = |Λ|`.

Direct corollaries of PR #2870 (`cardA_add_cardNotA_eq_card`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool)

/-- **`|¬A| = 0 → |A| = |Λ|`**. -/
theorem cardA_eq_card_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (Finset.univ.filter (fun x : Λ => A x = true)).card =
      Fintype.card Λ := by
  have := cardA_add_cardNotA_eq_card (Λ := Λ) A
  omega

/-- **`|A| = 0 → |¬A| = |Λ|`**. -/
theorem cardNotA_eq_card_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      Fintype.card Λ := by
  have := cardA_add_cardNotA_eq_card (Λ := Λ) A
  omega

end LatticeSystem.Quantum
