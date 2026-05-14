import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Maximum-Casimir `(Ŝ_tot)²` eigenspace is invariant under any
Heisenberg `H_J`

For any coupling `J : V → V → ℂ`, the Heisenberg Hamiltonian
`heisenbergHamiltonianS J N` commutes with `(Ŝ_tot)²` (SU(2)
invariance), so it preserves every `(Ŝ_tot)²`-eigenspace. In
particular, the maximum-Casimir eigenspace is invariant:

  `Submodule.map H_J.mulVecLin ((Ŝ_tot)² eigenspace at max Casimir)
     ≤ (Ŝ_tot)² eigenspace at max Casimir`.

This is the A-independent, J-independent invariance statement
underlying PRs #2808 / #2809 (which combine it with the saturated-
case identification to give the predicted-GS invariance).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **Max-Casimir (Ŝ_tot)² eigenspace is invariant under any H_J**:
for any coupling `J`,
`Submodule.map (heisenbergHamiltonianS J N).mulVecLin
(Module.End.eigenspace (Ŝ_tot)².mulVecLin
(saturatedFerromagnetCasimirEigenvalueS V N))
≤ Module.End.eigenspace (Ŝ_tot)².mulVecLin
(saturatedFerromagnetCasimirEigenvalueS V N)`. -/
theorem totalSpinSSquaredEigenspace_max_heisenbergHamiltonianS_invariant
    (J : V → V → ℂ) :
    Submodule.map (heisenbergHamiltonianS (Λ := V) J N).mulVecLin
        (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N)) ≤
      Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) := by
  rintro w ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hv
  rw [Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  rw [show (totalSpinSSquared V N).mulVec
        ((heisenbergHamiltonianS (Λ := V) J N).mulVec v) =
      (heisenbergHamiltonianS (Λ := V) J N).mulVec
        ((totalSpinSSquared V N).mulVec v) from by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        (heisenbergHamiltonianS_commute_totalSpinSSquared
          (Λ := V) J N).symm.eq]]
  rw [hv, Matrix.mulVec_smul]

end LatticeSystem.Quantum
