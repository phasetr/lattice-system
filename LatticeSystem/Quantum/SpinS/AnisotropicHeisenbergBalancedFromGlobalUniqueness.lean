import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinLeSectorMin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorInverseLift
import LatticeSystem.Quantum.SpinS.Theorem24ZeroMagnetizationFromUniqueness

/-!
# Balanced SU(2) sector ground energy from global uniqueness

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

If the full SU(2)-point ground eigenspace is one-dimensional and
`M_balanced` has zero centered magnetization, then the balanced sector attains
the full ground energy at `(λ, D) = (1, 0)`.

Proof: take a full ground eigenvector, use the zero-magnetization theorem from
global uniqueness, restrict it to the balanced sector, and compare the sector
minimum with the full minimum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Balanced SU(2) sector attains the full ground energy from global
uniqueness**: if the full ground eigenspace of `Ĥ(1,0)` has `finrank ≤ 1`, then
any sector whose centered magnetization is zero has sector minimum equal to the
full minimum. -/
theorem hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced_center :
      ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) :
            ℝ) : ℂ)) ≤ 1) :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) := by
  classical
  set Efull := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)
  set Ebal := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0)
  set H := anisotropicHeisenbergS (Λ := Λ) J (1 : ℂ) (0 : ℂ) N
  -- Choose a non-zero full ground eigenvector at the SU(2) endpoint.
  obtain ⟨Φ, hΦ_ne, hΦ_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)
  have hΦ_eig_Efull : H.mulVec Φ = ((Efull : ℝ) : ℂ) • Φ := by
    simpa [H, Efull] using hΦ_eig
  -- Global uniqueness forces zero total `S^3` magnetization.
  have hzero : (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
    exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
      (Λ := Λ) (N := N) J 1 0 ((Efull : ℝ) : ℂ)
      (by simpa [Efull] using h_global_unique) hΦ_ne hΦ_eig_Efull
  have hΦ_mem_zero : Φ ∈ magSubspaceS Λ N 0 := by
    rw [mem_magSubspaceS_iff]
    simpa using hzero
  have hΦ_mem_balanced : Φ ∈ magSubspaceS Λ N
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ)) := by
    simpa [h_balanced_center] using hΦ_mem_zero
  have h_embed_restrict :
      magSectorEmbedding (magSectorRestriction (M := M_balanced) Φ) = Φ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS hΦ_mem_balanced
  have hrestrict_ne : magSectorRestriction (M := M_balanced) Φ ≠ 0 := by
    intro hzero_restrict
    apply hΦ_ne
    have h := h_embed_restrict
    rw [hzero_restrict, magSectorEmbedding_zero] at h
    exact h.symm
  -- The balanced restriction is a non-zero sector eigenvector at the full
  -- ground energy, hence the balanced sector minimum is at most the full one.
  have hsec_eig :
      (anisotropicHeisenbergS_magSector_submatrix
        (Λ := Λ) J (1 : ℂ) (0 : ℂ) N M_balanced).mulVec
          (magSectorRestriction (M := M_balanced) Φ) =
        ((Efull : ℝ) : ℂ) • magSectorRestriction (M := M_balanced) Φ :=
    anisotropicHeisenbergS_magSector_submatrix_mulVec_magSectorRestriction_of_full_eigen
      J (1 : ℂ) (0 : ℂ) (M := M_balanced) hΦ_eig_Efull
  have hsec_Herm := anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
    (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0
  have hne_bot : End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix
        (Λ := Λ) J (1 : ℂ) (0 : ℂ) N M_balanced))
      ((Efull : ℝ) : ℂ) ≠ ⊥ := by
    intro hbot
    apply hrestrict_ne
    have hmem : magSectorRestriction (M := M_balanced) Φ ∈
        End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS_magSector_submatrix
            (Λ := Λ) J (1 : ℂ) (0 : ℂ) N M_balanced))
          ((Efull : ℝ) : ℂ) := by
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hsec_eig
    rw [hbot] at hmem
    exact hmem
  have hHE : End.HasEigenvalue (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix
        (Λ := Λ) J (1 : ℂ) (0 : ℂ) N M_balanced))
      ((Efull : ℝ) : ℂ) := hne_bot
  have h_mem_C : ((Efull : ℝ) : ℂ) ∈ spectrum ℂ
      (anisotropicHeisenbergS_magSector_submatrix
        (Λ := Λ) J (1 : ℂ) (0 : ℂ) N M_balanced) := by
    rw [← Matrix.spectrum_toLin']
    exact hHE.mem_spectrum
  have h_mem_R : Efull ∈ spectrum ℝ
      (anisotropicHeisenbergS_magSector_submatrix
        (Λ := Λ) J (1 : ℂ) (0 : ℂ) N M_balanced) := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]
    exact h_mem_C
  change Efull ∈ spectrum ℝ
      (anisotropicHeisenbergS_magSector_submatrix
        (Λ := Λ) J ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) N M_balanced) at h_mem_R
  rw [hsec_Herm.spectrum_real_eq_range_eigenvalues] at h_mem_R
  obtain ⟨i, hi⟩ := h_mem_R
  have hsector_le_full : Ebal ≤ Efull := by
    rw [← hi]
    exact hermitian_min_eigenvalue_le hsec_Herm i
  have hfull_le_sector : Efull ≤ Ebal := by
    simpa [Efull, Ebal] using
      hermitianMinEigenvalue_anisotropicHeisenbergS_full_le_sector
        (Λ := Λ) hJ N M_balanced 1 0
  exact le_antisymm hsector_le_full hfull_le_sector

end LatticeSystem.Quantum
