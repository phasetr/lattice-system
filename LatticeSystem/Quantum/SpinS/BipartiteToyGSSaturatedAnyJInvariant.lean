import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqCasimirEigenspaceSaturated
import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Predicted GS at saturated case is invariant under ANY Heisenberg
Hamiltonian `H_J`

At the saturated edge case `|¬A| = 0`, the predicted GS subspace
equals the maximum-Casimir `(Ŝ_tot)²`-eigenspace (PR #2802). Since
any Heisenberg Hamiltonian `heisenbergHamiltonianS J N` commutes
with `(Ŝ_tot)²` (SU(2) invariance,
`heisenbergHamiltonianS_commute_totalSpinSSquared`), it preserves
this eigenspace and hence the predicted GS:

  `Submodule.map H_J.mulVecLin (predicted GS) ≤ predicted GS`

at the saturated case, for **any** coupling `J : Λ → Λ → ℂ`.

This generalises PR #2794 (`Ĥ_toy_S`-invariance at the general
case) to ANY Heisenberg Hamiltonian, specifically at the saturated
case.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS at saturated case is invariant under any
`heisenbergHamiltonianS J N`**: at `|¬A| = 0` and for any coupling
`J`,
`Submodule.map (heisenbergHamiltonianS J N).mulVecLin
(bipartiteToyGroundStateSubspacePredicted A N) ≤
bipartiteToyGroundStateSubspacePredicted A N`. -/
theorem bipartiteToyGroundStateSubspacePredicted_heisenbergHamiltonianS_invariant_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool) (J : Λ → Λ → ℂ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    Submodule.map (heisenbergHamiltonianS (Λ := Λ) J N).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  -- At the saturated case, predicted GS = (Ŝ_tot)² eigenspace at max Casimir.
  rw [bipartiteToyGroundStateSubspacePredicted_eq_totalSpinSSquaredEigenspace_of_cardNotA_zero
        A h]
  -- Goal: Submodule.map H_J.mulVecLin ((Ŝ_tot)² eigenspace) ≤
  --       ((Ŝ_tot)² eigenspace).
  rintro w ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hv
  rw [Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  -- (Ŝ_tot)² · (H_J · v) = H_J · ((Ŝ_tot)² · v) via commute.
  rw [show (totalSpinSSquared Λ N).mulVec
        ((heisenbergHamiltonianS (Λ := Λ) J N).mulVec v) =
      (heisenbergHamiltonianS (Λ := Λ) J N).mulVec
        ((totalSpinSSquared Λ N).mulVec v) from by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        (heisenbergHamiltonianS_commute_totalSpinSSquared
          (Λ := Λ) J N).symm.eq]]
  rw [hv, Matrix.mulVec_smul]

end LatticeSystem.Quantum
