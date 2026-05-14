import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqSpanLadderSaturated

/-!
# Predicted GS at opposite saturated case = span of ladder iterates

Mirror of PR #2804 for the orientation `|A| = 0`. Apply PR #2804
to `¬A` with `|¬¬A| = 0` reducing to `|A| = 0` via filter
congruence:

  `bipartiteToyGroundStateSubspacePredicted (¬A) N
     = Submodule.span ℂ (Set.range (ladderIterateUp Λ N))`

when `|A| = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS at opposite saturated case = span of ladder
iterates**: when `|A| = 0`,
`bipartiteToyGroundStateSubspacePredicted (¬A) N =
Submodule.span ℂ (Set.range (ladderIterateUp Λ N))`. Mirror of
PR #2804 via orientation flip. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_eq_span_ladderIterateUp_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N =
      Submodule.span ℂ (Set.range (ladderIterateUp Λ N)) := by
  apply bipartiteToyGroundStateSubspacePredicted_eq_span_ladderIterateUp_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
