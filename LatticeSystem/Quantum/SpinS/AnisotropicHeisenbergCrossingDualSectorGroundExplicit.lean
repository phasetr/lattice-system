import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorGroundEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricGapCrossingGeneric

/-!
# Dual sector ground full-eigenvectors at parametric IVT crossing (explicit μ form)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Variant of the PR #3972 generic crossing dual-sector eigenvector wrapper
(since removed) whose conclusion eliminates the inner `∃ μ : ℝ` by replacing
the existential with the explicit value `hermitianMinEigenvalue (Ĥ_M_0(γ(t*)))`.

This form lets downstream proofs avoid the opaque-existential-μ issue and
enables the obligation (2) capstone wiring at the global-min energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Explicit-μ dual sector ground at parametric IVT crossing**: under the IVT
crossing hypotheses, produces a crossing point `t* ∈ [0, 1]` and nonzero sector
eigenvectors `Φ_M_0`, `Φ_M` at the SPECIFIC energy
`hermitianMinEigenvalue (Ĥ_M_0(γ(t*)))`. -/
theorem anisotropicHeisenbergS_crossing_dual_sector_ground_eigenvectors_explicit
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
      (∃ Φ_M0 : magConfigS Λ N M_0 → ℂ, Φ_M0 ≠ 0 ∧
        (anisotropicHeisenbergS J
            ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N).mulVec
          (magSectorEmbedding Φ_M0) =
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ
              (anisotropicHeisenbergParametricPath lam' D' t).1
              (anisotropicHeisenbergParametricPath lam' D' t).2) : ℝ) : ℂ) •
            magSectorEmbedding Φ_M0 ∧
        magSectorEmbedding Φ_M0 ∈ magSubspaceS Λ N
          (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_0 : ℂ))) ∧
      (∃ Φ_M : magConfigS Λ N M → ℂ, Φ_M ≠ 0 ∧
        (anisotropicHeisenbergS J
            ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N).mulVec
          (magSectorEmbedding Φ_M) =
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ
              (anisotropicHeisenbergParametricPath lam' D' t).1
              (anisotropicHeisenbergParametricPath lam' D' t).2) : ℝ) : ℂ) •
            magSectorEmbedding Φ_M ∧
        magSectorEmbedding Φ_M ∈ magSubspaceS Λ N
          (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ))) := by
  -- Get the crossing t* from PR #3971's IVT (this gives the EQUALITY of sector min eigenvalues).
  obtain ⟨t, htmem, hteq⟩ :=
    anisotropicHeisenbergS_parametric_gap_crossing_generic
      (Λ := Λ) hJ N M_0 M lam' D' h0 h1
  refine ⟨t, htmem, ?_, ?_⟩
  · -- Sector M_0 ground full-eigenvector at the sector-M_0 min energy.
    exact exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 N M_0
  · -- Sector M ground full-eigenvector at the sector-M min energy; rewrite via hteq
    -- to express at the sector-M_0 min energy (= sector-M min by hteq).
    obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2 N M
    refine ⟨Φ_M, hΦ_M_ne, ?_, hΦ_M_mem⟩
    -- hΦ_M_eig has (sector-M min) coefficient; hteq : sector-M_0 min = sector-M min.
    -- Convert by rewriting backwards.
    rw [← hteq] at hΦ_M_eig
    exact hΦ_M_eig

end LatticeSystem.Quantum
