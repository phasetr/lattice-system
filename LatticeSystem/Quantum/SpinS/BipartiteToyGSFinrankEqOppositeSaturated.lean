import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankEqSaturated

/-!
# Predicted GS subspace finrank EQUALITY at the opposite saturated case

Mirror of PR #2792 for the opposite orientation `|A| = 0`.
Applying PR #2792 to the flipped sublattice `¬A` (with
`|¬¬A| = 0` reducing to `|A| = 0` via filter congruence) gives:

  `Module.finrank ℂ
       (bipartiteToyGroundStateSubspacePredicted (¬A) N)
     = Fintype.card Λ * N + 1`

when `|A| = 0`. Confirms the complement-orientation predicted GS
subspace at the opposite saturated case is also exactly the
`(2 m_max + 1)`-dim spin-`m_max` irrep.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Finrank equality at opposite saturated case**: when `|A| = 0`,
`finrank(bipartiteToyGroundStateSubspacePredicted (¬A) N) = |V|·N + 1`.
Mirror of PR #2792 via the orientation flip. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_finrank_eq_succ_card_mul_N_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    Module.finrank ℂ
      (bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N) =
        Fintype.card Λ * N + 1 := by
  apply bipartiteToyGroundStateSubspacePredicted_finrank_eq_succ_card_mul_N_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
