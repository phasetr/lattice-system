import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Linear equivalence between sector vectors and sector subspace

(PR #3908, Issue #3739): the LinearEquiv between sector-indexed vectors
`magConfigS Λ N M → ℂ` and the corresponding sector subspace
`magSubspaceS Λ N (|Λ|·N/2 - M)`.

This is the bridge that lets within-sector-matrix `finrank ≤ 1` results
transfer to the full Hilbert space `⊓ sector subspace` form needed for the
SU(2) symmetric `finrank ≤ 1` capstone toward Tasaki §2.5 Theorem 2.4.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector LinearEquiv**: `magConfigS Λ N M → ℂ ≃ₗ[ℂ] magSubspaceS Λ N (|Λ|·N/2 - M)`.

Forward: `magSectorEmbedding` lifts a sector vector to a full Hilbert space
vector supported on the sector. Backward: `magSectorRestriction` restricts to
the sector. -/
noncomputable def magSectorLinearEquiv (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (N : ℕ) (M : ℕ) :
    (magConfigS Λ N M → ℂ) ≃ₗ[ℂ]
      ↥(magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) where
  toFun Φ := ⟨magSectorEmbedding Φ, magSectorEmbedding_mem_magSubspaceS Φ⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    exact magSectorEmbedding_add Φ Ψ
  map_smul' c Φ := by
    apply Subtype.ext
    exact magSectorEmbedding_smul c Φ
  invFun f := magSectorRestriction (M := M) f.val
  left_inv Φ := magSectorRestriction_magSectorEmbedding Φ
  right_inv f := by
    apply Subtype.ext
    exact magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS f.2

end LatticeSystem.Quantum
