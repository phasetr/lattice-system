import LatticeSystem.Quantum.SpinS.PredictedGSEqJointCasimirEigenspaceSaturated

/-!
# Complement mirror at `|A| = 0`: predicted GS = joint Casimir eigenspace

PR #2925 proved that at `|¬A| = 0`, the predicted GS subspace equals
the joint sublattice-Casimir eigenspace under orientation `A`. The
complement mirror applies the result to orientation `¬A` with the
filter identity `|¬¬A| = |A| = 0`:

  `bipartiteToyGroundStateSubspacePredicted (fun x => ! A x) N
     = jointSublatticeCasimirEigenspace (fun x => ! A x) N`
  at `|A| = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Predicted GS = joint Casimir eigenspace** at saturated complement
`|A| = 0` (complement-orientation form). -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_eq_joint_complement_eigenspace_of_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) (fun x => ! A x) N =
      jointSublatticeCasimirEigenspace (Λ := Λ) (fun x => ! A x) N := by
  apply bipartiteToyGroundStateSubspacePredicted_eq_joint_eigenspace_of_cardNotA_zero
    (fun x => ! A x) N
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
