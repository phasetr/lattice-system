import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Cartesian-axis invariances of the predicted toy-Hamiltonian GS subspace

Following PR #2798 (Ŝ^(3)_tot / Ŝ^z_tot invariance), this file
adds the analogous invariances under Ŝ^(1)_tot and Ŝ^(2)_tot. The
predicted GS subspace `bipartiteToyGroundStateSubspacePredicted A N`
is closed under each Cartesian component of the total spin:

  `Submodule.map (Ŝ^(α)_tot).mulVecLin (predicted GS) ≤ predicted GS`
   for α ∈ {1, 2, 3}.

(α = 3 was PR #2798; this PR handles α = 1, 2.)

Proof: each `Ŝ^(α)_tot` commutes with all three Casimirs:
* `totalSpinSSquared_commute_totalSpinSOp{1,2}` for `(Ŝ_tot)²`.
* `sublatticeSpinSquaredS_commute_totalSpinSOp{1,2}` for `(Ŝ_A)²`,
  applied to `A` and `¬A` for the two sublattice cases.

Combined with the per-Casimir invariance pattern, gives the
predicted GS invariance. Reflects the SU(2)-symmetry of the
predicted GS subspace under the full Cartesian spin algebra (a
necessary structural condition for it to carry an irreducible
SU(2) representation, which is the §2.5 Theorem 2.3 prediction).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **`Ŝ^(1)_tot`-invariance of the predicted GS subspace**: same
pattern as PR #2798, with all commutations
`{totalSpin,sublatticeSpin}SquaredS_commute_totalSpinSOp1`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSOp1_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOp1 Λ N).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨⟨h_tot, h_A⟩, h_B⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_tot
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_B
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (totalSpinSSquared Λ N).mulVec
          ((totalSpinSOp1 Λ N).mulVec v) =
        (totalSpinSOp1 Λ N).mulVec ((totalSpinSSquared Λ N).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (totalSpinSSquared_commute_totalSpinSOp1 (V := Λ) (N := N)).symm.eq]]
    rw [h_tot, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec
          ((totalSpinSOp1 Λ N).mulVec v) =
        (totalSpinSOp1 Λ N).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp1 (Λ := Λ) N A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((totalSpinSOp1 Λ N).mulVec v) =
        (totalSpinSOp1 Λ N).mulVec
          ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp1
            (Λ := Λ) N (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

set_option linter.style.longLine false in
/-- **`Ŝ^(2)_tot`-invariance of the predicted GS subspace**: same
pattern as PR #2798, with `_commute_totalSpinSOp2` lemmas. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSOp2_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOp2 Λ N).mulVecLin
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  rintro w ⟨v, hv, rfl⟩
  obtain ⟨⟨h_tot, h_A⟩, h_B⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_tot
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at h_B
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (totalSpinSSquared Λ N).mulVec
          ((totalSpinSOp2 Λ N).mulVec v) =
        (totalSpinSOp2 Λ N).mulVec ((totalSpinSSquared Λ N).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (totalSpinSSquared_commute_totalSpinSOp2 (V := Λ) (N := N)).symm.eq]]
    rw [h_tot, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec
          ((totalSpinSOp2 Λ N).mulVec v) =
        (totalSpinSOp2 Λ N).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp2 (Λ := Λ) N A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((totalSpinSOp2 Λ N).mulVec v) =
        (totalSpinSOp2 Λ N).mulVec
          ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp2
            (Λ := Λ) N (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

end LatticeSystem.Quantum
