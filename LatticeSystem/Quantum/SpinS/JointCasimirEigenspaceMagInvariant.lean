import LatticeSystem.Quantum.SpinS.JointCasimirEigenspaceLadderInvariant

/-!
# `Ŝ³_tot`-invariance of the joint sublattice-Casimir eigenspace

Scaffold for the minimal-total-spin joint eigenstate (Issue #3674, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The joint maximal-sublattice-Casimir eigenspace `W = jointSublatticeCasimirEigenspace A N`
is invariant under `Ŝ³_tot` (both sublattice Casimirs commute with it), so it is
graded by the total magnetization: `W = ⊕_M (W ⊓ magSubspaceS V N M)`.  Together
with the ladder invariance (#3684), this makes `W` an `su(2)`-subrepresentation,
the setting for the rank-nullity argument producing the minimal-total-spin
highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`Ŝ³_tot`-invariance of the joint sublattice-Casimir eigenspace**. -/
theorem jointSublatticeCasimirEigenspace_totalSpinSOp3_invariant (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOp3 Λ N).mulVecLin
        (jointSublatticeCasimirEigenspace (Λ := Λ) A N) ≤
      jointSublatticeCasimirEigenspace (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨h_A, h_B⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h_B
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOp3 Λ N).mulVec v) =
        (totalSpinSOp3 Λ N).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp3 (Λ := Λ) (N := N) A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ((totalSpinSOp3 Λ N).mulVec v) =
        (totalSpinSOp3 Λ N).mulVec ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp3 (Λ := Λ) (N := N)
            (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

end LatticeSystem.Quantum
