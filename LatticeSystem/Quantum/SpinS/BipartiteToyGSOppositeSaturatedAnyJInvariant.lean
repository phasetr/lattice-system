import LatticeSystem.Quantum.SpinS.BipartiteToyGSSaturatedAnyJInvariant

/-!
# Predicted GS at opposite saturated case invariant under any
Heisenberg `H_J`

Mirror of PR #2808 for the opposite orientation `|A| = 0`. Apply
PR #2808 to `¬A` with `|¬¬A| = 0` reducing to `|A| = 0` via filter
congruence.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS at opposite saturated case is invariant under
any `heisenbergHamiltonianS J N`**: for any coupling `J` and
`|A| = 0`,
`Submodule.map H_J.mulVecLin (bipartiteToyGroundStateSubspacePredicted (¬A) N)
  ≤ bipartiteToyGroundStateSubspacePredicted (¬A) N`. Mirror of
PR #2808 via orientation flip. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_heisenbergHamiltonianS_invariant_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool) (J : Λ → Λ → ℂ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    Submodule.map (heisenbergHamiltonianS (Λ := Λ) J N).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
          (fun x => ! A x) N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N := by
  apply bipartiteToyGroundStateSubspacePredicted_heisenbergHamiltonianS_invariant_of_cardNotA_zero
    (fun x => ! A x) J
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
