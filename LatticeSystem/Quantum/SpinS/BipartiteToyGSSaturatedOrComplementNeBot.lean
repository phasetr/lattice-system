import LatticeSystem.Quantum.SpinS.BipartiteToyGSSaturatedNeBot

/-!
# Predicted GS subspace at either saturated edge is non-trivial

Unifies PR #2820's two ne_bot statements (saturated at `|¬A| = 0`
and complement at `|A| = 0`) into a single disjunctive lemma:

  `|A| = 0 ∨ |¬A| = 0 → bipartiteToyGroundStateSubspacePredicted A N ≠ ⊥`.

The complement orientation is handled by selecting `(fun x => ! A x)`
when `|A| = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS subspace at either saturated edge is non-trivial**:
when `|¬A| = 0`, `bipartiteToyGroundStateSubspacePredicted A N ≠ ⊥`
directly (PR #2820's saturated branch). -/
theorem bipartiteToyGroundStateSubspacePredicted_ne_bot_of_saturated_edge
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≠ ⊥ ∨
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N ≠ ⊥ := by
  rcases h with hA | hAc
  · exact Or.inr
      (bipartiteToyGroundStateSubspacePredicted_complement_ne_bot_of_cardA_zero
        A hA)
  · exact Or.inl
      (bipartiteToyGroundStateSubspacePredicted_ne_bot_of_cardNotA_zero
        A hAc)

end LatticeSystem.Quantum
