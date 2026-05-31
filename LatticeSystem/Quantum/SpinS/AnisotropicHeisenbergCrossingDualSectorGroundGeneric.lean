import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorGroundEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricGapCrossingGeneric

/-!
# Generic-`M_0` dual sector ground full-eigenvectors at parametric IVT crossing

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Generic-`M_0` variant of PR #3964
(`anisotropicHeisenbergS_crossing_dual_sector_ground_eigenvectors`) using PR
#3971's generic-`M_0` IVT crossing. Needed by the Tasaki §2.5 Theorem 2.4
application with `M_0 = balanced` for `|A| = |B|`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Generic-`M_0` dual sector ground full-eigenvectors at parametric crossing**: under
the IVT-crossing hypotheses (strict gap at `(1, 0)` and inequality at `(λ', D')`),
produces a crossing `t*` and a common eigenvalue `μ` such that both sectors
`M_0` and `M` carry nonzero ground full-eigenvectors of `Ĥ(γ(t*))` at `μ`,
with corresponding `Ŝ³_tot` eigenspace membership. -/
theorem anisotropicHeisenbergS_crossing_dual_sector_ground_eigenvectors_generic
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_0 M : ℕ)
    [Nonempty (magConfigS Λ N M)] [Nonempty (magConfigS Λ N M_0)]
    (lam' D' : ℝ)
    (h0 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ 1 0) <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ 1 0))
    (h1 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ lam' D') ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ lam' D')) :
    ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
      ∃ μ : ℝ,
        (∃ Φ_M0 : magConfigS Λ N M_0 → ℂ, Φ_M0 ≠ 0 ∧
          (anisotropicHeisenbergS J
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N).mulVec
            (magSectorEmbedding Φ_M0) =
            (μ : ℂ) • magSectorEmbedding Φ_M0 ∧
          magSectorEmbedding Φ_M0 ∈ magSubspaceS Λ N
            (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_0 : ℂ))) ∧
        (∃ Φ_M : magConfigS Λ N M → ℂ, Φ_M ≠ 0 ∧
          (anisotropicHeisenbergS J
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N).mulVec
            (magSectorEmbedding Φ_M) =
            (μ : ℂ) • magSectorEmbedding Φ_M ∧
          magSectorEmbedding Φ_M ∈ magSubspaceS Λ N
            (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ))) := by
  obtain ⟨t, htmem, hteq⟩ :=
    anisotropicHeisenbergS_parametric_gap_crossing_generic (Λ := Λ) hJ N M_0 M lam' D' h0 h1
  refine ⟨t, htmem, hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_0) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2), ?_, ?_⟩
  · obtain ⟨Φ_M0, hΦ_M0_ne, hΦ_M0_eig, hΦ_M0_mem⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2 N M_0
    exact ⟨Φ_M0, hΦ_M0_ne, hΦ_M0_eig, hΦ_M0_mem⟩
  · obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2 N M
    refine ⟨Φ_M, hΦ_M_ne, ?_, hΦ_M_mem⟩
    rw [← hteq] at hΦ_M_eig
    exact hΦ_M_eig

end LatticeSystem.Quantum
