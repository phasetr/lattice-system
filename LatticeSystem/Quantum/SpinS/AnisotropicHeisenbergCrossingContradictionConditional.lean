import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Theorem24FinrankLeTwoContradiction

/-!
# Sector-embedded two-eigenvector contradiction conditional on `finrank ≤ 2`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) IVT crossing argument.

`magSectorEmbedding`-flavoured wrapper of
`anisotropicHeisenbergS_finrank_le_two_no_admis_plus_nonadmis` (PR #3903):
given two nonzero sector vectors `Φ_admis : magConfigS Λ N M_admis → ℂ` and
`Φ_nonadmis : magConfigS Λ N M_nonadmis → ℂ` whose embeddings are both
eigenvectors of `Ĥ(λ, D)` at the same energy `μ`, with the sector indices
matching admissible (`|V|·N/2 - M_admis = 0`) and non-admissible
(`|V|·N/2 - M_nonadmis ≠ 0`), an obligation (1) `finrank ≤ 2` bound at `μ`
forces `False`.

Combines:
- The two `magSectorEmbedding` → `magSubspaceS` membership bridge
  (`magSectorEmbedding_mem_magSubspaceS`).
- PR #3903's `finrank ≤ 2` reflection contradiction.
- A simple non-vanishing check for `magSectorEmbedding`.

This is the final algebraic step of the IVT crossing argument; the input
sector eigenvectors at the crossing point were supplied by PR #3964's
crossing dual-sector eigenvector construction (since removed; the crossing
route was completed via a separate wiring).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Embedded two-sector eigenvector contradiction at finrank ≤ 2**: given
nonzero sector vectors `Φ_admis : magConfigS Λ N M_admis → ℂ` (centered-zero
sector) and `Φ_nonadmis : magConfigS Λ N M_nonadmis → ℂ` (non-centered-zero
sector) whose embeddings are both eigenvectors of `Ĥ(λ, D)` at the same energy
`μ`, an obligation (1) `finrank ≤ 2` bound at `μ` produces `False`.

This is the magSectorEmbedding-bridge form of PR #3903's reflection contradiction
`anisotropicHeisenbergS_finrank_le_two_no_admis_plus_nonadmis`. The
sector→full eigenvector lift was established in PR #3961
(`anisotropicHeisenbergS_mulVec_magSectorEmbedding`). -/
theorem anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    (J : Λ → Λ → ℂ) (lam D μ : ℂ)
    (h_finrank : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2)
    {M_admis : ℕ} {Φ_admis : magConfigS Λ N M_admis → ℂ}
    (hΦ_admis_ne : Φ_admis ≠ 0)
    (h_admis_zero : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_admis : ℂ) = 0)
    (hΦ_admis_eig : (anisotropicHeisenbergS J lam D N).mulVec
        (magSectorEmbedding Φ_admis) = μ • magSectorEmbedding Φ_admis)
    {M_nonadmis : ℕ} {Φ_nonadmis : magConfigS Λ N M_nonadmis → ℂ}
    (hΦ_nonadmis_ne : Φ_nonadmis ≠ 0)
    (h_nonadmis_ne_zero :
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_nonadmis : ℂ)) ≠ 0)
    (hΦ_nonadmis_eig : (anisotropicHeisenbergS J lam D N).mulVec
        (magSectorEmbedding Φ_nonadmis) = μ • magSectorEmbedding Φ_nonadmis) :
    False := by
  classical
  -- magSubspaceS membership for both embeddings.
  have hΦ_admis_subspace : magSectorEmbedding Φ_admis ∈ magSubspaceS Λ N 0 := by
    rw [← h_admis_zero]
    exact magSectorEmbedding_mem_magSubspaceS Φ_admis
  have hΦ_nonadmis_subspace : magSectorEmbedding Φ_nonadmis ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_nonadmis : ℂ)) :=
    magSectorEmbedding_mem_magSubspaceS Φ_nonadmis
  -- Non-vanishing of the embeddings.
  have hΦ_admis_embed_ne : magSectorEmbedding Φ_admis ≠ 0 := by
    intro h
    apply hΦ_admis_ne
    funext τ
    have := congrFun h τ.1
    rwa [magSectorEmbedding_apply_subtype Φ_admis τ] at this
  have hΦ_nonadmis_embed_ne : magSectorEmbedding Φ_nonadmis ≠ 0 := by
    intro h
    apply hΦ_nonadmis_ne
    funext τ
    have := congrFun h τ.1
    rwa [magSectorEmbedding_apply_subtype Φ_nonadmis τ] at this
  -- Apply PR #3903 reflection + ≤2 contradiction.
  exact anisotropicHeisenbergS_finrank_le_two_no_admis_plus_nonadmis
    J lam D μ h_finrank hΦ_admis_subspace hΦ_admis_embed_ne hΦ_admis_eig
    h_nonadmis_ne_zero hΦ_nonadmis_subspace hΦ_nonadmis_embed_ne hΦ_nonadmis_eig

end LatticeSystem.Quantum
