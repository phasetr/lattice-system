import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingContradictionConditional
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinLeSectorMin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue

/-!
# Strict gap at `(1, 0)` from SU(2) global uniqueness

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

This is the structural replacement for the single strict-gap axiom used by the
spin-1/2 obligation-(2) capstone.  If the full SU(2) ground eigenspace at
`(λ, D) = (1, 0)` has `finrank ≤ 1`, the balanced sector attains the global
minimum, and every sector different from `M_balanced` has non-zero centered
magnetization, then every such sector has strictly larger energy at `(1, 0)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict gap at `(1, 0)` from global SU(2) uniqueness**: if the full
SU(2)-point ground eigenspace has dimension at most one and the balanced sector
attains the full minimum, then any non-balanced sector with non-zero centered
magnetization has strictly larger sector minimum.

The proof is by contradiction.  Equality for a non-balanced sector would produce
two non-zero sector ground vectors at the full minimum, one in centered
magnetization `0` and one in a non-zero centered magnetization.  The existing
two-sector/reflection contradiction rules this out under `finrank ≤ 2`; the
`finrank ≤ 1` hypothesis gives that bound immediately. -/
theorem strict_gap_at_SU2_of_global_unique
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    [Nonempty (Λ → Fin (N + 1))]
    (h_balanced_center :
      ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (h_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) : ℝ) : ℂ)) ≤ 1)
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)) :
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) <
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ 1 0) := by
  classical
  set Efull := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)
  set Ebal := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0)
  set EM := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M) hJ 1 0)
  have hfull_le_M :
      Efull ≤ EM := by
    simpa [Efull, EM] using
      hermitianMinEigenvalue_anisotropicHeisenbergS_full_le_sector
        (Λ := Λ) hJ N M 1 0
  have hbal_eq_full : Ebal = Efull := by
    simpa [Ebal, Efull] using h_GS_at_SU2
  have hfull_lt_M : Efull < EM := by
    refine lt_of_le_of_ne hfull_le_M ?_
    intro h_eq
    -- Balanced sector ground vector, lifted to the full Hilbert space at `Efull`.
    obtain ⟨Φbal, hΦbal_ne, hΦbal_eig, _⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS
        (Λ := Λ) hJ 1 0 N M_balanced
    -- Non-balanced sector ground vector, also lifted to the full Hilbert space at `Efull`
    -- under the contradictory equality `Efull = EM`.
    obtain ⟨ΦM, hΦM_ne, hΦM_eig, _⟩ :=
      exists_sectorGround_full_eigenvector_anisotropicHeisenbergS
        (Λ := Λ) hJ 1 0 N M
    have hΦbal_eig_full :
        (anisotropicHeisenbergS J (1 : ℂ) (0 : ℂ) N).mulVec
          (magSectorEmbedding Φbal) =
        ((Efull : ℝ) : ℂ) • magSectorEmbedding Φbal := by
      have hE : Ebal = Efull := hbal_eq_full
      simpa [Ebal, Efull, hE] using hΦbal_eig
    have hΦM_eig_full :
        (anisotropicHeisenbergS J (1 : ℂ) (0 : ℂ) N).mulVec
          (magSectorEmbedding ΦM) =
        ((Efull : ℝ) : ℂ) • magSectorEmbedding ΦM := by
      have hE : EM = Efull := h_eq.symm
      simpa [EM, Efull, hE] using hΦM_eig
    have h_finrank_le_two :
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
          ((Efull : ℝ) : ℂ)) ≤ 2 := by
      exact le_trans (by simpa [Efull] using h_global_unique) (by norm_num)
    exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
      J 1 0 ((Efull : ℝ) : ℂ) h_finrank_le_two
      hΦbal_ne h_balanced_center hΦbal_eig_full
      hΦM_ne h_centered_nonzero hΦM_eig_full
  rw [hbal_eq_full]
  exact hfull_lt_M

/-- **Strict gap at γ(0) from global SU(2) uniqueness, path-named form**:
the same result as `strict_gap_at_SU2_of_global_unique`, expressed through
`anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath` for
direct use by the Theorem 2.4 deformation capstones. -/
theorem strict_gap_at_path_zero_of_global_unique
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    [Nonempty (Λ → Fin (N + 1))]
    (lam' D' : ℝ)
    (h_balanced_center :
      ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (h_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) : ℝ) : ℂ)) ≤ 1)
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D' 0 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M lam' D' 0 := by
  have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
  simp only [hpath]
  exact strict_gap_at_SU2_of_global_unique hJ N M_balanced M
    h_balanced_center h_centered_nonzero h_global_unique h_GS_at_SU2

end LatticeSystem.Quantum
