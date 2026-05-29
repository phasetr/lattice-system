import LatticeSystem.Quantum.SpinS.SectorEmbeddingComplexEigval
import LatticeSystem.Quantum.SpinS.SectorRestrictionComplexEigval
import LatticeSystem.Quantum.SpinS.MagSectorLinearEquiv

/-!
# Sector matrix eigenspace and full Hilbert eigenspace ⊓ sector subspace: finrank equality

(PR #3912, Issue #3739): finrank equality between the sector matrix
`heisenbergHamiltonianSMatrixOnMagSector`'s μ-eigenspace and the full Hilbert
`heisenbergHamiltonianS`'s μ-eigenspace ⊓ sector subspace. Combines PR #3908
(`magSectorLinearEquiv`), PR #3910 (ℂ restriction), and PR #3911 (ℂ embedding).

This is the within-admissible PF input transfer lemma, the final piece of the
SU(2) symmetric `finrank ≤ 1` capstone chain toward Tasaki §2.5 Theorem 2.4
obligation (2.a).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Submodule

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Eigenspace finrank equality between sector matrix and full Hilbert ⊓ sector**. -/
theorem heisenbergHamiltonianS_sector_matrix_eigenspace_finrank_eq
    (J : Λ → Λ → ℂ) (M : ℕ) (μ : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) =
      finrank ℂ ↥((End.eigenspace (Matrix.toLin'
          (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ⊓
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) := by
  classical
  -- LinearEquiv between the two eigenspaces.
  let fwd : ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) →ₗ[ℂ]
        ↥((End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ⊓
          magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) := {
    toFun := fun Φ => ⟨magSectorEmbedding Φ.val, by
      refine ⟨?_, ?_⟩
      · -- magSectorEmbedding Φ.val ∈ full eigenspace at μ.
        simp only [SetLike.mem_coe, End.mem_eigenspace_iff, Matrix.toLin'_apply]
        have hΦ_mem := Φ.property
        simp only [End.mem_eigenspace_iff, Matrix.toLin'_apply] at hΦ_mem
        exact heisenbergHamiltonianS_mulVec_magSectorEmbedding_complex
          J Φ.val hΦ_mem
      · exact magSectorEmbedding_mem_magSubspaceS Φ.val⟩
    map_add' := fun Φ Ψ => by
      apply Subtype.ext
      exact magSectorEmbedding_add Φ.val Ψ.val
    map_smul' := fun c Φ => by
      apply Subtype.ext
      exact magSectorEmbedding_smul c Φ.val
  }
  let bwd : ↥((End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ⊓
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) →ₗ[ℂ]
      ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) := {
    toFun := fun f => ⟨magSectorRestriction (M := M) f.val, by
      simp only [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hf_in : Matrix.toLin' (heisenbergHamiltonianS J N) f.val = μ • f.val :=
        End.mem_eigenspace_iff.mp f.property.1
      rw [Matrix.toLin'_apply] at hf_in
      exact
        heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen_complex
        J hf_in⟩
    map_add' := fun f g => by
      apply Subtype.ext
      funext τ
      rfl
    map_smul' := fun c f => by
      apply Subtype.ext
      funext τ
      rfl
  }
  -- LinearEquiv construction.
  let equiv : ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) ≃ₗ[ℂ]
      ↥((End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ⊓
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

end LatticeSystem.Quantum
