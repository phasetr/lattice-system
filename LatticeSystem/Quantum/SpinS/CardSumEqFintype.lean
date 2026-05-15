import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# `|A| + |¬A| = |Λ|` (the bipartition cardinality sum)

For any predicate-induced bipartition `A : Λ → Bool`, the
cardinalities of the two filter-subsets sum to `|Λ|`:

  `|A| + |¬A| = Fintype.card Λ`.

A foundational identity used across the γ-4 chain to bridge
between `|A|`, `|¬A|`, and `|Λ|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool)

/-- Filter-set complement bridge: `{x | (!A x) = true} = {x | ¬(A x = true)}`
as `Finset` filters. -/
theorem filter_notA_eq_filter_not_A_eq_true :
    Finset.univ.filter (fun x : Λ => (! A x) = true) =
      Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
  classical
  congr 1
  funext x
  rcases hA : A x <;> simp [hA]

/-- **Bipartition cardinality sum**: `|A| + |¬A| = Fintype.card Λ`. -/
theorem cardA_add_cardNotA_eq_card :
    (Finset.univ.filter (fun x : Λ => A x = true)).card +
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      Fintype.card Λ := by
  classical
  rw [filter_notA_eq_filter_not_A_eq_true, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : Λ => A x = true)

end LatticeSystem.Quantum
