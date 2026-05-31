import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSectorZero
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuity
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Sector → full eigenvector lift for the anisotropic Hamiltonian

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

A sector eigenvector of the anisotropic Hamiltonian's magnetization-`M`
submatrix `anisotropicHeisenbergS_magSector_submatrix` at eigenvalue `μ`
lifts to a full-Hilbert-space eigenvector of `anisotropicHeisenbergS J λ D N`
at the same `μ`, via zero-extension outside the sector
(`magSectorEmbedding`).

This is the anisotropic analogue of `heisenbergHamiltonianS_mulVec_magSectorEmbedding`
(in `MagSectorEmbedding.lean`); proof uses the same pattern, relying on the
sector-crossing matrix-element vanishing
(`anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne` from PR #3898).

Used by the obligation (2) IVT crossing argument capstone: at the crossing
point `p*`, sector ground eigenvectors at the common min energy lift to full
eigenvectors, then the reflection (`Θ`) + obligation (1) contradiction
(PR #3903) closes the chain.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector → full eigenvector lift**: a sector eigenvector
`Φ : magConfigS Λ N M → ℂ` of the anisotropic Hamiltonian's sector submatrix at
eigenvalue `μ : ℂ` lifts via `magSectorEmbedding` to a full-Hilbert-space
eigenvector of `anisotropicHeisenbergS J lam D N` at the same `μ`.

Proof: pointwise on `σ : Λ → Fin (N + 1)`.
- If `σ ∈ sector M`: the `mulVec` sum reduces to a sector sum since matrix
  elements between configurations of different `magSumS` vanish
  (`anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne`).
- If `σ ∉ sector M`: both sides vanish — LHS because every term in the
  `mulVec` sum is zero (either the embedding is zero outside the sector, or
  the Hamiltonian matrix element vanishes between configurations of different
  `magSumS`); RHS because the embedding is zero. -/
theorem anisotropicHeisenbergS_mulVec_magSectorEmbedding
    (J : Λ → Λ → ℂ) (lam D : ℂ) {M : ℕ}
    (Φ : magConfigS Λ N M → ℂ)
    {μ : ℂ}
    (hΦ : (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M).mulVec Φ =
      μ • Φ) :
    (anisotropicHeisenbergS J lam D N).mulVec (magSectorEmbedding Φ) =
      μ • (magSectorEmbedding Φ) := by
  classical
  funext σ
  by_cases hσ : magSumS σ = M
  · -- σ ∈ sector M. Reduce the full mulVec sum to a sector sum.
    -- LHS: ∑ ρ, H σ ρ * embed Φ ρ.
    -- Off-sector ρ: embed Φ ρ = 0. In-sector ρ: embed Φ ρ = Φ ⟨ρ, _⟩.
    -- So LHS = ∑_{ρ ∈ sector M} H σ ρ * Φ ⟨ρ, _⟩ = (submatrix H).mulVec Φ ⟨σ, hσ⟩.
    have hLHS_sub :
        (anisotropicHeisenbergS J lam D N).mulVec (magSectorEmbedding Φ) σ =
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M).mulVec Φ
          ⟨σ, hσ⟩ := by
      show ∑ ρ, (anisotropicHeisenbergS J lam D N) σ ρ * magSectorEmbedding Φ ρ =
        ∑ ρ' : magConfigS Λ N M,
          anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M ⟨σ, hσ⟩ ρ' *
            Φ ρ'
      -- Convert RHS sum to a sum of `H σ ρ'.1 * embed Φ ρ'.1` over magConfigS.
      have hRHS : (∑ ρ' : magConfigS Λ N M,
          anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M ⟨σ, hσ⟩ ρ' *
            Φ ρ') =
        ∑ ρ' : magConfigS Λ N M,
          (anisotropicHeisenbergS J lam D N) σ ρ'.1 * magSectorEmbedding Φ ρ'.1 := by
        refine Finset.sum_congr rfl (fun ρ' _ => ?_)
        unfold anisotropicHeisenbergS_magSector_submatrix
        rw [Matrix.submatrix_apply, magSectorEmbedding_apply_subtype]
      rw [hRHS]
      -- Convert LHS sum to filter sum (since embed is zero outside sector M).
      have hLHS_filter :
          (∑ ρ, (anisotropicHeisenbergS J lam D N) σ ρ * magSectorEmbedding Φ ρ) =
          ∑ ρ ∈ Finset.univ.filter (fun ρ : Λ → Fin (N + 1) => magSumS ρ = M),
            (anisotropicHeisenbergS J lam D N) σ ρ * magSectorEmbedding Φ ρ := by
        refine (Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_).symm
        intro ρ _ hne
        by_contra h
        apply hne
        rw [magSectorEmbedding_apply_of_not_mem Φ h, mul_zero]
      rw [hLHS_filter]
      -- Reindex filter sum to ∑ over magConfigS.
      rw [Finset.sum_subtype
        (Finset.univ.filter (fun ρ : Λ → Fin (N + 1) => magSumS ρ = M))
        (p := fun ρ => magSumS ρ = M)
        (fun ρ => by simp [Finset.mem_filter])
        (fun ρ => (anisotropicHeisenbergS J lam D N) σ ρ * magSectorEmbedding Φ ρ)]
      rfl
    rw [hLHS_sub]
    -- Now apply the sector eigenvalue equation.
    have hμ := congrFun hΦ ⟨σ, hσ⟩
    rw [hμ]
    show μ * Φ ⟨σ, hσ⟩ = (μ • magSectorEmbedding Φ) σ
    rw [Pi.smul_apply, magSectorEmbedding_apply_of_mem Φ hσ, smul_eq_mul]
  · -- σ ∉ sector M. Both sides vanish.
    have hLHS_zero :
        (anisotropicHeisenbergS J lam D N).mulVec (magSectorEmbedding Φ) σ = 0 := by
      show ∑ ρ, (anisotropicHeisenbergS J lam D N) σ ρ * magSectorEmbedding Φ ρ = 0
      refine Finset.sum_eq_zero (fun ρ _ => ?_)
      by_cases hρ : magSumS ρ = M
      · -- ρ ∈ sector M, σ ∉ sector M: magSums differ ⟹ matrix element = 0.
        have hne : magSumS σ ≠ magSumS ρ :=
          fun heq => hσ (heq.trans hρ)
        rw [anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne J lam D hne, zero_mul]
      · rw [magSectorEmbedding_apply_of_not_mem Φ hρ, mul_zero]
    rw [hLHS_zero]
    show (0 : ℂ) = (μ • magSectorEmbedding Φ) σ
    rw [Pi.smul_apply, magSectorEmbedding_apply_of_not_mem Φ hσ, smul_zero]

end LatticeSystem.Quantum
