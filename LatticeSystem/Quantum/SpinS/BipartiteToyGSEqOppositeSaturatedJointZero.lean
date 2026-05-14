import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqSaturatedJointZero

/-!
# Opposite-orientation submodule equality at `J = 0`

Mirror of PR #2796 for the orientation `|A| = 0`. Applying
PR #2796 to the flipped sublattice `¬A` (with `|¬¬A| = 0`
reducing to `|A| = 0` via filter congruence) gives:

  `bipartiteToyGroundStateSubspacePredicted (¬A) N
     = saturatedFerromagnetJointEigenspace 0 N`

when `|A| = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Submodule equality at opposite saturated case**: when
`|A| = 0`,
`bipartiteToyGroundStateSubspacePredicted (¬A) N =
saturatedFerromagnetJointEigenspace 0 N`. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_eq_saturatedFerromagnetJointEigenspace_zero_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ)
        (fun x => ! A x) N =
      saturatedFerromagnetJointEigenspace (V := Λ) (0 : Λ → Λ → ℂ) N := by
  apply bipartiteToyGroundStateSubspacePredicted_eq_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
    (fun x => ! A x) (N := N)
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
