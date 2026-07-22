import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceNeBot
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder

/-!
# Ladder invariance of the maximal sublattice-Casimir eigenspace

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The maximal `(Ŝ_A)²`-eigenspace (the A-symmetric subspace) is invariant under the
sublattice ladder operators `Ŝ_A^+`, `Ŝ_A^-` (the sublattice Casimir commutes with
them).  Together with non-triviality (#3688), it therefore contains the whole
`Ŝ_A^-`-ladder orbit of the all-up state — the spanning set of the A-symmetric
subspace, with one state per `A`-magnetization (the sublattice analogue of the §2.4
`TotalSpinSSquaredMaxEigenspace*` structure).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`Ŝ_A^-`-invariance of the maximal sublattice-Casimir eigenspace**. -/
theorem sublatticeMaxCasimirEigenspace_sublatticeSpinSOpMinus_invariant (A : Λ → Bool) (M : ℂ) :
    Submodule.map (sublatticeSpinSOpMinus N A).mulVecLin
        (Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin M) ≤
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin M := by
  rintro w ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  rw [show (sublatticeSpinSquaredS N A).mulVec ((sublatticeSpinSOpMinus N A).mulVec v) =
      (sublatticeSpinSOpMinus N A).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus (Λ := Λ) (N := N) A).symm.eq]]
  rw [hv, Matrix.mulVec_smul]

/-- **`Ŝ_A^+`-invariance of the maximal sublattice-Casimir eigenspace**. -/
theorem sublatticeMaxCasimirEigenspace_sublatticeSpinSOpPlus_invariant (A : Λ → Bool) (M : ℂ) :
    Submodule.map (sublatticeSpinSOpPlus N A).mulVecLin
        (Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin M) ≤
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin M := by
  rintro w ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  rw [show (sublatticeSpinSquaredS N A).mulVec ((sublatticeSpinSOpPlus N A).mulVec v) =
      (sublatticeSpinSOpPlus N A).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        (sublatticeSpinSquaredS_commute_sublatticeSpinSOpPlus (Λ := Λ) (N := N) A).symm.eq]]
  rw [hv, Matrix.mulVec_smul]

end LatticeSystem.Quantum
