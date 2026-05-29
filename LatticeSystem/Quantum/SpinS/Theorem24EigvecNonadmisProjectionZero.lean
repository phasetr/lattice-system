import LatticeSystem.Quantum.SpinS.Theorem24FinrankLeTwoContradiction
import LatticeSystem.Quantum.SpinS.AnisotropicSectorProjectionEigenvector

/-!
# Eigvec at μ has zero projection onto non-admissible sectors
(under `finrank ≤ 2` + admissible eigvec exists)

(PR #3904, Issue #3739): if the anisotropic Hamiltonian has `finrank ≤ 2` at
energy `μ` AND an admissible-sector eigenvector exists at `μ`, then for any
eigenvector `Ψ` at `μ`, the sector projection of `Ψ` onto any non-admissible
sector `M` (i.e., `2M ≠ |Λ|·N`) is `0`.

Direct contrapositive of PR #3903: a non-zero projection would yield a non-zero
non-admissible-sector eigenvector at `μ`, contradicting PR #3903.

This is the penultimate step toward the SU(2) symmetric `finrank ≤ 1`
result: combined with the magnetization-sector decomposition
`eq_sum_magSectorEmbedding_magSectorRestriction`, the eigenspace at `μ` is
contained in the admissible sector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Eigvec non-admissible projection is zero (under finrank ≤ 2 + admis. eigvec)**:
for any eigenvector `Ψ` at `μ`, the sector projection of `Ψ` onto any
non-admissible sector `M` (with `2M ≠ |Λ|·N`) is `0`. -/
theorem anisotropicHeisenbergS_eigvec_nonadmis_projection_zero
    (J : Λ → Λ → ℂ) (lam D μ : ℂ)
    (h_finrank : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J lam D N).mulVec Φ = μ • Φ)
    {Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΨ_eig : (anisotropicHeisenbergS J lam D N).mulVec Ψ = μ • Ψ)
    (M : ℕ) (hM_nonadmis : 2 * M ≠ Fintype.card Λ * N) :
    magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0 := by
  classical
  set w := magSectorEmbedding (magSectorRestriction (M := M) Ψ) with hwdef
  -- w is an eigenvector at μ via PR #3899.
  have hw_eig : (anisotropicHeisenbergS J lam D N).mulVec w = μ • w :=
    anisotropicHeisenbergS_magSectorProjection_eigen J lam D μ M hΨ_eig
  -- w is in magSubspaceS at non-admissible eigenvalue M' := |Λ|·N/2 - M.
  set M' : ℂ := ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ) with hM'def
  have hw_nonadmis : w ∈ magSubspaceS Λ N M' := by
    rw [hwdef, hM'def]
    exact magSectorEmbedding_mem_magSubspaceS _
  -- M' ≠ 0 since 2M ≠ |Λ|·N.
  have hM'_ne : M' ≠ 0 := by
    intro h_eq
    apply hM_nonadmis
    rw [hM'def] at h_eq
    have h_eq' : ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 = (M : ℂ) := by linear_combination h_eq
    have h_double : ((Fintype.card Λ : ℂ) * (N : ℂ)) = 2 * (M : ℂ) := by
      linear_combination 2 * h_eq'
    have : (2 * M : ℂ) = (Fintype.card Λ * N : ℂ) := by
      rw [show (2 * M : ℂ) = 2 * (M : ℂ) by push_cast; ring]
      rw [show (Fintype.card Λ * N : ℂ) = (Fintype.card Λ : ℂ) * (N : ℂ) by push_cast; ring]
      exact h_double.symm
    exact_mod_cast this
  -- Suppose w ≠ 0 for contradiction.
  by_contra hw_ne
  -- Apply PR #3903 with Ψ := w to get False.
  exact anisotropicHeisenbergS_finrank_le_two_no_admis_plus_nonadmis
    J lam D μ h_finrank hΦ_admis hΦ_ne hΦ_eig hM'_ne hw_nonadmis hw_ne hw_eig

end LatticeSystem.Quantum
