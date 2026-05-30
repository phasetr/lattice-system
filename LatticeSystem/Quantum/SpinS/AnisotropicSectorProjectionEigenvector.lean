import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSectorZero
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Sector projection of an anisotropic-Hamiltonian eigenvector is an eigenvector

(PR #3899, Issue #3739): for an eigenvector `v` of the anisotropic Heisenberg
Hamiltonian at eigenvalue `μ`, the sector projection
`magSectorEmbedding (magSectorRestriction (M:=M) v)` is also an eigenvector at
the same `μ`. This follows immediately from PR #3898's sector-crossing
matrix-element vanishing: only same-sector entries survive in the `mulVec`
expansion.

Vector-level analog of PR #3898 — enables sector-by-sector spectral analysis of
the anisotropic Hamiltonian, key building block toward Theorem 2.4 obligation
(2.a) uniqueness via sector decomposition.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector projection of an eigenvector is an eigenvector**: for an eigenvector
`v` of the anisotropic Hamiltonian at `μ`, the projection
`magSectorEmbedding (magSectorRestriction (M:=M) v)` (which equals `v` on sector
`M` and is `0` elsewhere) is also an eigenvector at `μ`. -/
theorem anisotropicHeisenbergS_magSectorProjection_eigen
    (J : Λ → Λ → ℂ) (lam D μ : ℂ) (M : ℕ)
    {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : (anisotropicHeisenbergS J lam D N).mulVec v = μ • v) :
    (anisotropicHeisenbergS J lam D N).mulVec
        (magSectorEmbedding (magSectorRestriction (M := M) v)) =
      μ • magSectorEmbedding (magSectorRestriction (M := M) v) := by
  classical
  set H := anisotropicHeisenbergS J lam D N with hHdef
  set w : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (magSectorRestriction (M := M) v) with hwdef
  funext σ
  by_cases hσM : magSumS σ = M
  · -- σ in sector M: (H·w) σ = (H·v) σ = μ · v σ = μ · w σ.
    have hw_σ : w σ = v σ := by
      rw [hwdef, magSectorEmbedding_magSectorRestriction_apply_of_mem _ hσM]
    -- (H·w) σ = ∑_τ H σ τ * w τ. For τ not in sector M, H σ τ = 0 (#3898).
    -- For τ in sector M, w τ = v τ. So (H·w) σ = ∑_{τ ∈ sector M} H σ τ * v τ.
    -- (H·v) σ = ∑_τ H σ τ * v τ = ∑_{τ ∈ sector M} H σ τ * v τ + ∑_{τ ∉ sector M} H σ τ * v τ.
    -- The second sum is 0 since H σ τ = 0 when sectors differ (#3898).
    -- So (H·w) σ = (H·v) σ = μ * v σ = μ * w σ.
    have hHwσ : H.mulVec w σ = H.mulVec v σ := by
      show ∑ τ, H σ τ * w τ = ∑ τ, H σ τ * v τ
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases hτM : magSumS τ = M
      · have : w τ = v τ := by
          rw [hwdef, magSectorEmbedding_magSectorRestriction_apply_of_mem _ hτM]
        rw [this]
      · -- σ in sector M, τ not in sector M: magSums differ, so H σ τ = 0.
        have hH0 : H σ τ = 0 := by
          rw [hHdef]
          exact anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne J lam D
            (fun heq => hτM (heq.symm.trans hσM))
        rw [hH0, zero_mul, zero_mul]
    rw [hHwσ, hv]
    have hμw : (μ • w) σ = μ * w σ := rfl
    have hμv : (μ • v) σ = μ * v σ := rfl
    rw [hμv, hμw, hw_σ]
  · -- σ not in sector M: (H·w) σ = 0 and (μ • w) σ = 0.
    have hw_σ_zero : w σ = 0 := by
      rw [hwdef]; exact magSectorEmbedding_apply_of_not_mem _ hσM
    -- (H·w) σ = ∑_τ H σ τ * w τ. For τ in sector M: σ ∉ M ⟹ H σ τ = 0.
    -- For τ not in sector M: w τ = 0. So all terms vanish.
    have hHwσ : H.mulVec w σ = 0 := by
      show ∑ τ, H σ τ * w τ = 0
      refine Finset.sum_eq_zero (fun τ _ => ?_)
      by_cases hτM : magSumS τ = M
      · have hH0 : H σ τ = 0 := by
          rw [hHdef]
          exact anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne J lam D
            (fun heq => hσM (heq.trans hτM))
        rw [hH0, zero_mul]
      · have : w τ = 0 := by
          rw [hwdef]; exact magSectorEmbedding_apply_of_not_mem _ hτM
        rw [this, mul_zero]
    rw [hHwσ]
    have : (μ • w) σ = μ * w σ := rfl
    rw [this, hw_σ_zero, mul_zero]

end LatticeSystem.Quantum
