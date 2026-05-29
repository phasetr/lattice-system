import LatticeSystem.Quantum.SpinS.Theorem24EigvecNonadmisProjectionZero
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Eigvec at μ is in the admissible sector
(under `finrank ≤ 2` + admissible eigvec exists)

(PR #3905, Issue #3739): combines PR #3904 (non-admissible projection is `0`)
with the magnetization-sector decomposition
`eq_sum_magSectorEmbedding_magSectorRestriction` to show that any eigvec `Ψ`
at energy `μ` lies in `magSubspaceS Λ N 0` (the `Ŝ³_tot = 0` admissible
sector), under the hypothesis that `finrank ≤ 2` at `μ` and that an admissible
eigvec exists at `μ`.

This is the final piece toward the SU(2) symmetric `finrank ≤ 1` argument:
combined with within-admissible-sector PF `finrank = 1`, the full Hilbert
space finrank at `μ` is `≤ 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Finset

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Eigvec at μ is in the admissible sector**: under `finrank ≤ 2` at `μ` and
existence of an admissible eigvec at `μ`, any eigvec `Ψ` at `μ` lies in
`magSubspaceS Λ N 0` (the `Ŝ³_tot = 0` admissible sector). -/
theorem anisotropicHeisenbergS_eigvec_in_admis_sector_of_finrank_le_two
    (J : Λ → Λ → ℂ) (lam D μ : ℂ)
    (h_finrank : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J lam D N).mulVec Φ = μ • Φ)
    {Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΨ_eig : (anisotropicHeisenbergS J lam D N).mulVec Ψ = μ • Ψ) :
    Ψ ∈ magSubspaceS Λ N 0 := by
  classical
  -- Decompose Ψ into sector projections.
  rw [eq_sum_magSectorEmbedding_magSectorRestriction Ψ]
  -- Each summand is in magSubspaceS Λ N 0 (either zero or admissible).
  refine Submodule.sum_mem _ ?_
  intro M _
  by_cases hM_admis : 2 * M = Fintype.card Λ * N
  · -- Admissible M: projection is in magSubspaceS Λ N (|Λ|·N/2 - M) = magSubspaceS Λ N 0.
    have hM'_zero : ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ) = 0 := by
      have h_cplx : ((2 * M : ℕ) : ℂ) = ((Fintype.card Λ * N : ℕ) : ℂ) := by
        exact_mod_cast hM_admis
      push_cast at h_cplx
      linear_combination -h_cplx / 2
    have h_mem : magSectorEmbedding (magSectorRestriction (M := M) Ψ) ∈
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) :=
      magSectorEmbedding_mem_magSubspaceS _
    rw [hM'_zero] at h_mem
    exact h_mem
  · -- Non-admissible M: projection is 0 (by PR #3904).
    have h_zero : magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0 :=
      anisotropicHeisenbergS_eigvec_nonadmis_projection_zero
        J lam D μ h_finrank hΦ_admis hΦ_ne hΦ_eig hΨ_eig M hM_admis
    rw [h_zero]
    exact (magSubspaceS Λ N 0).zero_mem

end LatticeSystem.Quantum
