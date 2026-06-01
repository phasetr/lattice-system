import LatticeSystem.Quantum.SpinS.AnisotropicEigenspaceSectorFinrankEq
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorGroundEigenvector
import LatticeSystem.Quantum.SpinS.Theorem24FinrankLeOneFromAdmisPF
import LatticeSystem.Quantum.SpinS.Theorem24ZeroMagnetizationFromUniqueness

/-!
# General spin-S target uniqueness conditional bridge

Issue #412 — Tasaki §2.5 Theorem 2.4.

This file extracts the final target-uniqueness linear-algebra step in the
general spin-`S` setting.  If the target full ground eigenspace has `finrank <= 2`,
the balanced sector attains the full ground energy, and the balanced sector
ground eigenspace is one-dimensional, then the full target ground eigenspace is
one-dimensional.  The zero-magnetization conclusion then follows from the
existing uniqueness-implies-zero-magnetization theorem.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **General spin-S target ground eigenspace `finrank <= 1` from balanced-sector
inputs**: full `finrank <= 2`, balanced-sector/full-ground equality, and
balanced-sector PF simplicity imply full target ground-state uniqueness. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_balanced_sector_pf
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2)
    (h_balanced_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix
          (Λ := Λ) J (lam : ℂ) (D : ℂ) N M_balanced))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) : ℝ) : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  set μ_sector : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) with hμ_sector_def
  set μ_full : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) with hμ_full_def
  have hμ_eq : ((μ_sector : ℝ) : ℂ) = ((μ_full : ℝ) : ℂ) := by
    rw [hμ_sector_def, hμ_full_def]
    exact congrArg (fun x : ℝ => (x : ℂ)) h_balanced_eq_full
  have h_admis_pf : finrank ℂ ↥((End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((μ_full : ℝ) : ℂ)) ⊓ magSubspaceS Λ N 0) ≤ 1 := by
    have h_transfer :=
      anisotropicHeisenbergS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
        (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ) M_balanced
        ((μ_sector : ℝ) : ℂ)
        (by simpa [hμ_sector_def] using h_balanced_sector_pf)
    rw [h_balanced] at h_transfer
    rw [hμ_eq] at h_transfer
    exact h_transfer
  obtain ⟨Φ_sector, hΦ_sector_ne, hΦ_eig, hΦ_admis⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS
      (Λ := Λ) hJ_star lam D N M_balanced
  set Φ : (Λ → Fin (N + 1)) → ℂ := magSectorEmbedding Φ_sector with hΦ_def
  have hΦ_ne : Φ ≠ 0 := by
    intro hzero
    apply hΦ_sector_ne
    have hres := congrArg
      (magSectorRestriction (V := Λ) (N := N) (M := M_balanced)) hzero
    simpa [hΦ_def, magSectorRestriction_magSectorEmbedding,
      magSectorRestriction_zero] using hres
  have hΦ_admis0 : Φ ∈ magSubspaceS Λ N 0 := by
    simpa [hΦ_def, h_balanced] using hΦ_admis
  have hΦ_eig_full :
      (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
        ((μ_full : ℝ) : ℂ) • Φ := by
    have hΦ_eig_sector :
        (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
          ((μ_sector : ℝ) : ℂ) • Φ := by
      simpa [hΦ_def, hμ_sector_def] using hΦ_eig
    rw [hμ_eq] at hΦ_eig_sector
    exact hΦ_eig_sector
  exact anisotropicHeisenbergS_finrank_le_one_from_admis_pf
    J (lam : ℂ) (D : ℂ) ((μ_full : ℝ) : ℂ)
    (by simpa [hμ_full_def] using h_full_le_two)
    hΦ_admis0 hΦ_ne hΦ_eig_full h_admis_pf

set_option linter.style.longLine false in
/-- **General spin-S target ground states have zero total magnetization from
balanced-sector inputs**: the target uniqueness bridge composed with the
existing uniqueness-implies-zero-magnetization theorem. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_balanced_sector_pf
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2)
    (h_balanced_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix
          (Λ := Λ) J (lam : ℂ) (D : ℂ) N M_balanced))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) : ℝ) : ℂ)) ≤ 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_balanced_sector_pf
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_balanced
      h_balanced_eq_full h_full_le_two h_balanced_sector_pf
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
