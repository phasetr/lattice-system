import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqCasimirEigenspaceSaturated
import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqCasimirEigenspaceOppositeSaturated
import LatticeSystem.Quantum.SpinS.TotalSpinSSquaredMaxEigenspaceNeBot

/-!
# Predicted GS subspace at saturated case is non-trivial

At the saturated edge case `|¬A| = 0`, the predicted GS subspace
equals the max-Casimir `(Ŝ_tot)²`-eigenspace, which is non-trivial
(contains `|σ_⊤⟩`). Hence:

  `bipartiteToyGroundStateSubspacePredicted A N ≠ ⊥`

when `|¬A| = 0`. Symmetric statement holds at `|A| = 0` for the
opposite orientation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS subspace at saturated case is non-trivial**:
`bipartiteToyGroundStateSubspacePredicted A N ≠ ⊥` when `|¬A| = 0`. -/
theorem bipartiteToyGroundStateSubspacePredicted_ne_bot_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≠ ⊥ := by
  rw [bipartiteToyGroundStateSubspacePredicted_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
        A h]
  exact totalSpinSSquaredEigenspace_max_ne_bot

set_option linter.style.longLine false in
/-- Opposite saturated mirror: `bipartiteToyGroundStateSubspacePredicted (¬A) N ≠ ⊥`
when `|A| = 0`. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_ne_bot_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N ≠ ⊥ := by
  apply bipartiteToyGroundStateSubspacePredicted_ne_bot_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
