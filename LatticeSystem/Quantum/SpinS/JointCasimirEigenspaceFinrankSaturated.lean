import LatticeSystem.Quantum.SpinS.PredictedGSEqJointCasimirEigenspaceSaturated
import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankEqSaturated

/-!
# Joint sublattice-Casimir eigenspace finrank at saturated: `|Λ|·N + 1`

PR #2925 proved that at `|¬A| = 0`, the predicted GS subspace
equals the joint sublattice-Casimir eigenspace. The existing
saturated-finrank PR
`bipartiteToyGroundStateSubspacePredicted_finrank_eq_succ_card_mul_N_of_cardNotA_zero`
gives `finrank (predicted GS) = |Λ|·N + 1` at `|¬A| = 0`. Hence

  `finrank (jointSublatticeCasimirEigenspace A N) = |Λ|·N + 1`
  at `|¬A| = 0`.

This is the dimension of the full SU(2) multiplet (2m_max + 1)
of the fully-polarised ferromagnetic state at saturated edges.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Joint Casimir eigenspace finrank at saturated `|¬A| = 0`**:
`finrank = |Λ|·N + 1`. -/
theorem jointSublatticeCasimirEigenspace_finrank_eq_succ_card_mul_N_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    Module.finrank ℂ (jointSublatticeCasimirEigenspace (Λ := Λ) A N) =
      Fintype.card Λ * N + 1 := by
  rw [← bipartiteToyGroundStateSubspacePredicted_eq_joint_eigenspace_of_cardNotA_zero
        A N h]
  exact bipartiteToyGroundStateSubspacePredicted_finrank_eq_succ_card_mul_N_of_cardNotA_zero
    A h

end LatticeSystem.Quantum
