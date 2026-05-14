import LatticeSystem.Quantum.SpinS.BipartiteToyGroundStateSaturated

/-!
# Complement mirror: `|σ_⊤⟩` is in the predicted GS at `|A| = 0`

`BipartiteToyGroundStateSaturated.lean` (PR #2782) already proves
the saturated-case witness:

  `|¬A| = 0 → allAlignedStateS Λ N 0 ∈
    bipartiteToyGroundStateSubspacePredicted A N`.

This file adds the complement mirror at `|A| = 0`: applying the
existing theorem to the orientation `(fun x => ! A x)` gives

  `|A| = 0 → allAlignedStateS Λ N 0 ∈
    bipartiteToyGroundStateSubspacePredicted (fun x => ! A x) N`.

The hypothesis transport uses the `¬¬A = A` filter congruence.
Pairs with PR #2820's complement ne_bot to give the explicit
witness `|σ_⊤⟩` at the `|A| = 0` edge.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Complement mirror at `|A| = 0`**: `|σ_⊤⟩` is in
`bipartiteToyGroundStateSubspacePredicted (fun x => ! A x) N`.
The original-orientation case (`|¬A| = 0`) lives in
`BipartiteToyGroundStateSaturated.lean` (PR #2782). -/
theorem allAlignedStateS_zero_mem_bipartiteToyGroundStateSubspacePredicted_complement_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (allAlignedStateS Λ N (0 : Fin (N + 1)) :
        (Λ → Fin (N + 1)) → ℂ) ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N := by
  apply allAlignedStateS_zero_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
