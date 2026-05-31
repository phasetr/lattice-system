import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorGroundEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricGapCrossing

/-!
# Dual sector ground full-eigenvectors at the parametric IVT crossing point

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) IVT crossing argument.

Composition of:
- `anisotropicHeisenbergS_parametric_gap_crossing` (PR #3959, the IVT crossing
  on `E_0(γ(t)) - E_M(γ(t))`).
- `exists_sectorGround_full_eigenvector_anisotropicHeisenbergS` (PR #3963,
  sector ground full-eigenvector existence).

Conclusion: at the crossing point `p* = γ(t*)`, both sectors `M_0 = 0` and `M`
have nonzero ground full-eigenvectors of the full anisotropic Hamiltonian
`Ĥ(p*)` at the COMMON minimum energy `μ_min(t*)`. Each lifts to the
corresponding `Ŝ³_tot` eigenspace.

This is the bridge step from the analytic IVT crossing to the algebraic
three-LI family at the crossing point (which then contradicts obligation
(1)'s `≤ 2` bound via the reflection symmetry).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Dual sector ground full-eigenvectors at the parametric crossing point**:
under the IVT-crossing hypotheses (strict gap at `(1, 0)` and inequality at
`(λ', D')`), there exists a crossing point `t* ∈ [0, 1]` and a common eigenvalue
`μ ∈ ℝ` such that both sectors `M_0 = 0` and `M` carry nonzero ground
full-eigenvectors of the full anisotropic Hamiltonian `Ĥ(γ(t*))` at `μ`. -/
theorem anisotropicHeisenbergS_crossing_dual_sector_ground_eigenvectors
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ)
    [Nonempty (magConfigS Λ N M)] [Nonempty (magConfigS Λ N 0)]
    (lam' D' : ℝ)
    (h0 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := 0) hJ 1 0) <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ 1 0))
    (h1 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ lam' D') ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := 0) hJ lam' D')) :
    ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
      ∃ μ : ℝ,
        (∃ Φ₀ : magConfigS Λ N 0 → ℂ, Φ₀ ≠ 0 ∧
          (anisotropicHeisenbergS J
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N).mulVec
            (magSectorEmbedding Φ₀) =
            (μ : ℂ) • magSectorEmbedding Φ₀ ∧
          magSectorEmbedding Φ₀ ∈ magSubspaceS Λ N
            ((Fintype.card Λ : ℂ) * (N : ℂ) / 2)) ∧
        (∃ Φ_M : magConfigS Λ N M → ℂ, Φ_M ≠ 0 ∧
          (anisotropicHeisenbergS J
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) N).mulVec
            (magSectorEmbedding Φ_M) =
            (μ : ℂ) • magSectorEmbedding Φ_M ∧
          magSectorEmbedding Φ_M ∈ magSubspaceS Λ N
            (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ))) := by
  -- IVT crossing: ∃ t ∈ [0, 1] with E_0(γ(t)) = E_M(γ(t)).
  obtain ⟨t, htmem, hteq⟩ :=
    anisotropicHeisenbergS_parametric_gap_crossing (Λ := Λ) hJ N M lam' D' h0 h1
  refine ⟨t, htmem, hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := 0) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2), ?_, ?_⟩
  · -- Sector 0 ground full-eigenvector.
    obtain ⟨Φ₀, hΦ₀_ne, hΦ₀_eig, hΦ₀_mem⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2 N 0
    refine ⟨Φ₀, hΦ₀_ne, hΦ₀_eig, ?_⟩
    have := hΦ₀_mem
    simp at this
    exact this
  · -- Sector M ground full-eigenvector, energy equal to sector 0 by hteq.
    obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2 N M
    refine ⟨Φ_M, hΦ_M_ne, ?_, hΦ_M_mem⟩
    rw [← hteq] at hΦ_M_eig
    exact hΦ_M_eig

end LatticeSystem.Quantum
