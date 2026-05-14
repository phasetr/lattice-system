import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Ladder-operator invariances of the predicted toy-Hamiltonian GS subspace

The predicted GS subspace is closed under the total raising and
lowering operators `Ŝ^+_tot` and `Ŝ^-_tot`. Combined with the
Cartesian invariances of PRs #2798 / #2799, this completes the
operator-level SU(2) closure of the predicted GS subspace under
the standard `su(2)` generators (Cartan + ladders).

Proof: each `Ŝ^±_tot = Ŝ^(1)_tot ± I · Ŝ^(2)_tot` so the
commutations with the three Casimirs follow from the Cartesian
versions via `Commute.add_right` / `Commute.sub_right` and
`Commute.smul_right`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `(Ŝ_A)²` commutes with `Ŝ^+_tot`. Derived from the Cartesian
commutations via `Ŝ^+_tot = Ŝ^(1)_tot + I · Ŝ^(2)_tot`. -/
theorem sublatticeSpinSquaredS_commute_totalSpinSOpPlus (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSOpPlus Λ N) := by
  rw [totalSpinSOpPlus_eq_add]
  exact (sublatticeSpinSquaredS_commute_totalSpinSOp1 (Λ := Λ) N A).add_right
    ((sublatticeSpinSquaredS_commute_totalSpinSOp2 (Λ := Λ) N A).smul_right
      Complex.I)

/-- `(Ŝ_A)²` commutes with `Ŝ^-_tot`. -/
theorem sublatticeSpinSquaredS_commute_totalSpinSOpMinus (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSOpMinus Λ N) := by
  rw [totalSpinSOpMinus_eq_sub]
  exact (sublatticeSpinSquaredS_commute_totalSpinSOp1 (Λ := Λ) N A).sub_right
    ((sublatticeSpinSquaredS_commute_totalSpinSOp2 (Λ := Λ) N A).smul_right
      Complex.I)

set_option linter.style.longLine false in
/-- **Ŝ^+_tot-invariance of the predicted GS subspace**. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSOpPlus_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOpPlus Λ N).mulVecLin
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
          ((totalSpinSOpPlus Λ N).mulVec v) =
        (totalSpinSOpPlus Λ N).mulVec ((totalSpinSSquared Λ N).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (totalSpinSSquared_commute_totalSpinSOpPlus
            (V := Λ) (N := N)).symm.eq]]
    rw [h_tot, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec
          ((totalSpinSOpPlus Λ N).mulVec v) =
        (totalSpinSOpPlus Λ N).mulVec
          ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpPlus
            (Λ := Λ) (N := N) A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((totalSpinSOpPlus Λ N).mulVec v) =
        (totalSpinSOpPlus Λ N).mulVec
          ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpPlus
            (Λ := Λ) (N := N) (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

set_option linter.style.longLine false in
/-- **Ŝ^-_tot-invariance of the predicted GS subspace**. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSOpMinus_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOpMinus Λ N).mulVecLin
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
          ((totalSpinSOpMinus Λ N).mulVec v) =
        (totalSpinSOpMinus Λ N).mulVec ((totalSpinSSquared Λ N).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (totalSpinSSquared_commute_totalSpinSOpMinus
            (V := Λ) (N := N)).symm.eq]]
    rw [h_tot, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec
          ((totalSpinSOpMinus Λ N).mulVec v) =
        (totalSpinSOpMinus Λ N).mulVec
          ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpMinus
            (Λ := Λ) (N := N) A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((totalSpinSOpMinus Λ N).mulVec v) =
        (totalSpinSOpMinus Λ N).mulVec
          ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOpMinus
            (Λ := Λ) (N := N) (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

end LatticeSystem.Quantum
