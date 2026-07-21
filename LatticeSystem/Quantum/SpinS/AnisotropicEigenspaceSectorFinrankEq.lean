import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorEmbeddingLift
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorInverseLift

/-!
# Anisotropic sector matrix eigenspace and full Hilbert eigenspace finrank transfer

Issue #3739 — Tasaki §2.5 Theorem 2.4.

This file is the anisotropic analogue of `EigenspaceSectorFinrankEq.lean` and
`EigenspaceFinrankLeOneTransfer.lean`.  The sector embedding/restriction maps
give a linear equivalence between the sector-matrix eigenspace of
`anisotropicHeisenbergS_magSector_submatrix` and the full Hilbert-space
eigenspace intersected with the corresponding magnetization subspace.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Submodule

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Anisotropic sector/full eigenspace finrank equality**: the eigenspace of
the sector matrix `Ĥ_M(λ,D)` at `μ` has the same finrank as the full eigenspace
of `Ĥ(λ,D)` at `μ` intersected with the corresponding magnetization subspace. -/
theorem anisotropicHeisenbergS_sector_matrix_eigenspace_finrank_eq
    (J : Λ → Λ → ℂ) (lam D : ℂ) (M : ℕ) (μ : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M)) μ) =
      finrank ℂ ↥((End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ⊓
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) := by
  classical
  let fwd : ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M)) μ) →ₗ[ℂ]
        ↥((End.eigenspace (Matrix.toLin'
            (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ⊓
          magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) := {
    toFun := fun Φ => ⟨magSectorEmbedding Φ.val, by
      refine ⟨?_, ?_⟩
      · simp only [SetLike.mem_coe, End.mem_eigenspace_iff, Matrix.toLin'_apply]
        have hΦ_mem := Φ.property
        simp only [End.mem_eigenspace_iff, Matrix.toLin'_apply] at hΦ_mem
        exact anisotropicHeisenbergS_mulVec_magSectorEmbedding
          J lam D Φ.val hΦ_mem
      · exact magSectorEmbedding_mem_magSubspaceS Φ.val⟩
    map_add' := fun Φ Ψ => by
      apply Subtype.ext
      exact magSectorEmbedding_add Φ.val Ψ.val
    map_smul' := fun c Φ => by
      apply Subtype.ext
      exact magSectorEmbedding_smul c Φ.val
  }
  let bwd : ↥((End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ⊓
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) →ₗ[ℂ]
      ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M)) μ) := {
    toFun := fun f => ⟨magSectorRestriction (M := M) f.val, by
      simp only [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hf_in : Matrix.toLin' (anisotropicHeisenbergS J lam D N) f.val =
          μ • f.val :=
        End.mem_eigenspace_iff.mp f.property.1
      rw [Matrix.toLin'_apply] at hf_in
      exact
        anisotropicHeisenbergS_magSector_submatrix_mulVec_magSectorRestriction_of_full_eigen
          J lam D hf_in⟩
    map_add' := fun f g => by
      apply Subtype.ext
      funext τ
      rfl
    map_smul' := fun c f => by
      apply Subtype.ext
      funext τ
      rfl
  }
  let equiv : ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M)) μ) ≃ₗ[ℂ]
      ↥((End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ⊓
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) := {
    fwd with
    invFun := bwd
    left_inv := fun Φ => by
      apply Subtype.ext
      exact magSectorRestriction_magSectorEmbedding Φ.val
    right_inv := fun f => by
      apply Subtype.ext
      exact magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS f.property.2
  }
  exact equiv.finrank_eq

/-- **Anisotropic sector matrix `finrank ≤ 1` transfer**: if the sector matrix's
`μ`-eigenspace has `finrank ≤ 1`, then the full Hilbert-space `μ`-eigenspace
intersected with the corresponding magnetization subspace also has
`finrank ≤ 1`. -/
theorem anisotropicHeisenbergS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
    (J : Λ → Λ → ℂ) (lam D : ℂ) (M : ℕ) (μ : ℂ)
    (h_sector : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M)) μ) ≤ 1) :
    finrank ℂ ↥((End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ⊓
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) ≤ 1 := by
  rw [← anisotropicHeisenbergS_sector_matrix_eigenspace_finrank_eq]
  exact h_sector

end LatticeSystem.Quantum
