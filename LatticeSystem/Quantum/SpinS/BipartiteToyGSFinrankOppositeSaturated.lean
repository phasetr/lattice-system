import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankSaturated

/-!
# Dimension lower bound on the predicted toy-H GS subspace
(opposite saturated edge case)

Mirror of PR #2787 for the orientation `|A| = 0` instead of
`|¬A| = 0`. In this case `bipartiteToyGroundStateSubspacePredicted A N`
is **not** the natural choice — the formula collapses to a
different (lower) (Ŝ_tot)² target eigenvalue since the
signed-difference imbalance `(s_A − s_B)` is negative.

Instead, the natural choice is the **complement-orientation**
predicted GS subspace `bipartiteToyGroundStateSubspacePredicted (¬A) N`,
which applies PR #2787 to the flipped sublattice (where
`|¬¬A| = 0` corresponds to the original `|A| = 0`).

This file packages the orientation-flipped finrank lower bound:

  `Fintype.card Λ * N + 1
     ≤ Module.finrank ℂ (bipartiteToyGroundStateSubspacePredicted (¬A) N)`

when `|A| = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS subspace finrank lower bound at the opposite
saturated case**: when `|A| = 0`, the complement-orientation
predicted GS subspace `bipartiteToyGroundStateSubspacePredicted (¬A) N`
has finrank `≥ |V|·N + 1`. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_finrank_ge_succ_card_mul_N_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    Fintype.card Λ * N + 1 ≤
      Module.finrank ℂ
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
          (fun x => ! A x) N) := by
  -- Apply PR #2787 to the flipped sublattice `¬A`. The hypothesis
  -- `card !(¬A) = 0` reduces to `card A = 0` via `¬¬A = A`.
  apply bipartiteToyGroundStateSubspacePredicted_finrank_ge_succ_card_mul_N_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  -- Goal: `card {x | (!!A x) = true} = 0`. Reduce to `card {x | A x = true} = 0`.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
