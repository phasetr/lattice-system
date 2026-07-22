import LatticeSystem.Quantum.SpinS.PredictedGSFinrankLtJointCasimirFinrank
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLadderInvariant

/-!
# Ladder invariance of the joint sublattice-Casimir eigenspace

Scaffold for the minimal-total-spin joint eigenstate (Issue #3674, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The joint maximal-sublattice-Casimir eigenspace
`W = jointSublatticeCasimirEigenspace A N` (`(Ŝ_A)² = s_A(s_A+1)` and
`(Ŝ_¬A)² = s_B(s_B+1)`) is invariant under the total ladder operators `Ŝ⁺_tot`,
`Ŝ⁻_tot`, since both sublattice Casimirs commute with them.  This is the carrier
on which the total spin `(Ŝ_tot)²` decomposes; the rank-nullity of `Ŝ⁺_tot` across
its magnetization grading yields the minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`Ŝ⁺_tot`-invariance of the joint sublattice-Casimir eigenspace**. -/
theorem jointSublatticeCasimirEigenspace_totalSpinSOpPlus_invariant (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOpPlus Λ N).mulVecLin
        (jointSublatticeCasimirEigenspace (Λ := Λ) A N) ≤
      jointSublatticeCasimirEigenspace (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨h_A, h_B⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h_B
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOpPlus Λ N).mulVec v) =
        (totalSpinSOpPlus Λ N).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpPlus (Λ := Λ) (N := N) A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ((totalSpinSOpPlus Λ N).mulVec v) =
        (totalSpinSOpPlus Λ N).mulVec ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpPlus (Λ := Λ) (N := N)
            (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

/-- **`Ŝ⁻_tot`-invariance of the joint sublattice-Casimir eigenspace**. -/
theorem jointSublatticeCasimirEigenspace_totalSpinSOpMinus_invariant (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOpMinus Λ N).mulVecLin
        (jointSublatticeCasimirEigenspace (Λ := Λ) A N) ≤
      jointSublatticeCasimirEigenspace (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨h_A, h_B⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h_B
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOpMinus Λ N).mulVec v) =
        (totalSpinSOpMinus Λ N).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpMinus (Λ := Λ) (N := N) A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ((totalSpinSOpMinus Λ N).mulVec v) =
        (totalSpinSOpMinus Λ N).mulVec
          ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpMinus (Λ := Λ) (N := N)
            (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

end LatticeSystem.Quantum
