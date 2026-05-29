import LatticeSystem.Quantum.SpinS.SectorEmbeddingComplexEigval
import LatticeSystem.Quantum.SpinS.SectorRestrictionComplexEigval
import LatticeSystem.Quantum.SpinS.MagSectorLinearEquiv

/-!
# Sector matrix eigenspace と full Hilbert eigenspace ⊓ sector subspace の finrank 等式

(PR #3912, Issue #3739): sector matrix `heisenbergHamiltonianSMatrixOnMagSector`
の μ-eigenspace と, full Hilbert `heisenbergHamiltonianS` の μ-eigenspace ⊓
sector subspace の `finrank` 等式. PR #3908 (`magSectorLinearEquiv`),
PR #3910 (ℂ restriction), PR #3911 (ℂ embedding) を組み合わせ.

これは within-admissible PF input の transfer に必要な lemma で,
SU(2) symmetric `finrank ≤ 1` capstone へ向かう Tasaki §2.5 Theorem 2.4
obligation (2.a) の chain の最終仕上げ.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Submodule

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector matrix と full Hilbert ⊓ sector の eigenspace finrank 等式**. -/
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
      simp only [SetLike.mem_coe, End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hf_in := f.property.1
      simp only [SetLike.mem_coe, End.mem_eigenspace_iff, Matrix.toLin'_apply] at hf_in
      exact heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen_complex
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
