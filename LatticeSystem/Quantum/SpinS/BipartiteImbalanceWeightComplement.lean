import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightInt

/-!
# Orientation flip of `bipartiteImbalanceWeight`

Swapping the bipartition orientation `A ↔ ¬A` negates the signed
imbalance:

  `bipartiteImbalanceWeight (fun x => ! A x) N
     = -bipartiteImbalanceWeight A N`.

This is the algebraic statement of "the complement orientation
has the opposite sign of the original orientation's signed
sublattice imbalance" — a building block for Tasaki §2.5 Theorem
2.3's orientation independence of the predicted total spin
magnitude `||A| − |¬A||·S` (PR #2826's norm form).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Orientation flip negates `bipartiteImbalanceWeight`**:
`bipartiteImbalanceWeight (fun x => ! A x) N
     = -bipartiteImbalanceWeight A N`. -/
theorem bipartiteImbalanceWeight_complement_eq_neg :
    bipartiteImbalanceWeight (Λ := Λ) (fun x => ! A x) N =
      -bipartiteImbalanceWeight (Λ := Λ) A N := by
  unfold bipartiteImbalanceWeight
  -- The filters swap: {x | ¬¬A x = true} = {x | A x = true} and vice versa.
  have hAA : (Finset.univ.filter (fun x : Λ => (! (! A x)) = true)) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  have hAcomp : (Finset.univ.filter (fun x : Λ => (! A x) = true)) =
      Finset.univ.filter (fun x : Λ => (! A x) = true) := rfl
  rw [hAA]
  ring

end LatticeSystem.Quantum
