import LatticeSystem.Quantum.SpinS.BipartiteToyGSEigenspaceBridge
import LatticeSystem.Quantum.SpinS.PredictedGSFinrankLtJointCasimirFinrank

/-!
# Predicted GS subspace EQUALS joint Casimir eigenspace at saturated

PR #2923 proved that at non-degenerate the joint sublattice-Casimir
eigenspace strictly contains the predicted GS subspace. At the
saturated edge `|¬A| = 0`, by contrast, the two coincide:

  `bipartiteToyGroundStateSubspacePredicted A N
     = jointSublatticeCasimirEigenspace A N`   at `|¬A| = 0`.

The forward inclusion `predicted GS ⊆ joint Casimir` holds by
definition of the predicted GS (intersection of three eigenspaces
including the two sublattice-Casimir constraints). The reverse
inclusion follows because at `|¬A| = 0`:
- `(Ŝ_¬A)² = 0` operator (PR `sublatticeSpinSquaredS_eq_zero_of_card_zero`),
  so its 0-eigenspace is the full ambient, redundant.
- `(Ŝ_A)² = (Ŝ_tot)²` (PR
  `sublatticeSpinSquaredS_eq_totalSpinSSquared_of_cardNotA_zero`),
  so `(Ŝ_A)²` eigenspace at `s_A(s_A+1)` equals `(Ŝ_tot)²` eigenspace
  at the predicted target.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Predicted GS = joint Casimir eigenspace at saturated `|¬A| = 0`**. -/
theorem bipartiteToyGroundStateSubspacePredicted_eq_joint_eigenspace_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N =
      jointSublatticeCasimirEigenspace (Λ := Λ) A N := by
  apply le_antisymm
  · -- ⊆: predicted GS is defined as intersection including both sublattice
    -- Casimir conditions, so it's contained in their intersection.
    intro v hv
    exact ⟨hv.1.2, hv.2⟩
  · -- ⊇: at saturated, joint Casimir ⊆ predicted GS. Use the existing
    -- eigenspace bridge: every (Ŝ_tot)² eigenvector at the predicted target
    -- is in predicted GS. At saturated, (Ŝ_A)² = (Ŝ_tot)², so (Ŝ_A)²-eigenspace
    -- at s_A·(s_A+1) IS the (Ŝ_tot)² eigenspace at that target.
    intro v hv
    apply totalSpinSSquaredEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
      A h
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    -- hv : v ∈ joint Casimir; extract the (Ŝ_A)² eigenspace condition.
    have hAv := hv.1
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply] at hAv
    rw [← sublatticeSpinSquaredS_eq_totalSpinSSquared_of_cardNotA_zero A h]
    exact hAv

end LatticeSystem.Quantum
