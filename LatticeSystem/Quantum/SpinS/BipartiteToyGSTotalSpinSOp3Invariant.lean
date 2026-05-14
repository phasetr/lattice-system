import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# `Ŝ^z_tot`-invariance of the predicted toy-Hamiltonian GS subspace

The predicted GS subspace `bipartiteToyGroundStateSubspacePredicted A N`
is invariant under the total magnetization operator `Ŝ^z_tot`:

  `Submodule.map (Ŝ^z_tot).mulVecLin (predicted GS) ≤ predicted GS`.

Proof: `Ŝ^z_tot` commutes with all three Casimirs (`(Ŝ_tot)²`,
`(Ŝ_A)²`, `(Ŝ_¬A)²`), so it preserves each Casimir eigenspace and
hence their meet (the predicted GS subspace).

This reflects the standard physical picture: a magnetization-
preserving operator commutes with the Casimir hierarchy and acts
within each fixed-Casimir subspace. In particular, the predicted
GS subspace at the saturated case (`|¬A| = 0`) is mapped to itself
under `Ŝ^z_tot` — consistent with its identification (via PR #2768
and PR #2796) as the saturated-ferromagnet joint eigenspace
carrying the `(2 m_max + 1)`-dim irreducible representation, which
*does* admit `Ŝ^z_tot` as an internal operator.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **`Ŝ^z_tot`-invariance of the predicted GS subspace**:
`Submodule.map Ŝ^z_tot.mulVecLin (bipartiteToyGroundStateSubspacePredicted A N)
  ≤ bipartiteToyGroundStateSubspacePredicted A N`.

Proof: `Ŝ^z_tot` commutes with each of the three Casimirs
(`totalSpinSSquared_commute_totalSpinSOp3` for the total Casimir
and `sublatticeSpinSquaredS_commute_totalSpinSOp3` applied to both
`A` and `¬A` for the sublattice Casimirs), so it preserves each
eigenspace and hence their meet. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSOp3_invariant
    (A : Λ → Bool) (N : ℕ) :
    Submodule.map (totalSpinSOp3 Λ N).mulVecLin
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
  · -- (Ŝ_tot)² · (Ŝ^z_tot · v) = Ŝ^z_tot · ((Ŝ_tot)² · v) via commute.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (totalSpinSSquared Λ N).mulVec
          ((totalSpinSOp3 Λ N).mulVec v) =
        (totalSpinSOp3 Λ N).mulVec ((totalSpinSSquared Λ N).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (totalSpinSSquared_commute_totalSpinSOp3 (Λ := Λ) N).symm.eq]]
    rw [h_tot, Matrix.mulVec_smul]
  · -- (Ŝ_A)² · (Ŝ^z_tot · v) = Ŝ^z_tot · ((Ŝ_A)² · v).
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N A).mulVec
          ((totalSpinSOp3 Λ N).mulVec v) =
        (totalSpinSOp3 Λ N).mulVec ((sublatticeSpinSquaredS N A).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp3 (Λ := Λ) N A).symm.eq]]
    rw [h_A, Matrix.mulVec_smul]
  · -- (Ŝ_¬A)² · (Ŝ^z_tot · v) = Ŝ^z_tot · ((Ŝ_¬A)² · v).
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [show (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((totalSpinSOp3 Λ N).mulVec v) =
        (totalSpinSOp3 Λ N).mulVec
          ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          (sublatticeSpinSquaredS_commute_totalSpinSOp3
            (Λ := Λ) N (fun x => ! A x)).symm.eq]]
    rw [h_B, Matrix.mulVec_smul]

end LatticeSystem.Quantum
