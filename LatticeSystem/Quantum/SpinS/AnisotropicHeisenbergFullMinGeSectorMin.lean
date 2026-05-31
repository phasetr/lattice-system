import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorInverseLift
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinLeSectorMin
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector

/-!
# Global Ĥ min ≥ some sector min (block-min identity, hard direction)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

For real-coupling `J` and real `(λ, D)`, there exists a non-empty sector `M`
such that `hermitianMinEigenvalue Ĥ_M(λ, D) ≤ hermitianMinEigenvalue Ĥ(λ, D)`.

Combined with PR #3984 (easy direction `hermitianMinEigenvalue Ĥ ≤ each sector min`),
this gives: there exists `M` (non-empty) with
`hermitianMinEigenvalue Ĥ_M = hermitianMinEigenvalue Ĥ`.

Proof: get a full-Ĥ eigvec `v` at the global min (PR #3962). Project to some
sector `M` where the projection is non-zero (`exists_magSectorRestriction_ne_zero`).
The restriction is a sector eigvec at the same energy (PR #3988 inverse lift).
Hence sector-`M` min ≤ global min.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Existence of a non-zero sector projection** for any non-zero full vector:
if `v ≠ 0`, then `∃ M`, `magSectorRestriction (M := M) v ≠ 0`. -/
theorem exists_magSectorRestriction_ne_zero
    {N : ℕ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ≠ 0) :
    ∃ M ∈ Finset.range (Fintype.card Λ * N + 1),
      magSectorRestriction (V := Λ) (N := N) (M := M) v ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hv
  have hsum := eq_sum_magSectorEmbedding_magSectorRestriction (V := Λ) (N := N) v
  rw [hsum]
  refine Finset.sum_eq_zero (fun M hM => ?_)
  rw [h M hM, magSectorEmbedding_zero]

/-- **Existence of a sector achieving the global min**: there is a non-empty
sector `M` with `hermitianMinEigenvalue Ĥ_M ≤ hermitianMinEigenvalue Ĥ`. -/
theorem exists_sector_hermitianMinEigenvalue_le_full
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N : ℕ) (lam D : ℝ) [Nonempty (Λ → Fin (N + 1))] :
    ∃ M : ℕ, ∃ _ : Nonempty (magConfigS Λ N M),
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ lam D) ≤
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D) := by
  classical
  -- Get a non-zero Ĥ eigvec at the full min.
  obtain ⟨v, hv_ne, hv_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D)
  -- v has a non-zero sector restriction at some M.
  obtain ⟨M, _hM_range, hvM_ne⟩ := exists_magSectorRestriction_ne_zero hv_ne
  -- The sector M is non-empty (restriction non-zero on subtype).
  haveI hNE : Nonempty (magConfigS Λ N M) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    apply hvM_ne
    funext τ
    exact (hempty.false τ).elim
  refine ⟨M, hNE, ?_⟩
  -- Sector restriction is a sector eigvec at the full min (PR #3988).
  set μ : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D) with hμ_def
  have hsec_eig := anisotropicHeisenbergS_magSector_submatrix_mulVec_magSectorRestriction_of_full_eigen
    J ((lam : ℂ)) ((D : ℂ)) (μ := ((μ : ℝ) : ℂ)) (M := M) hv_eig
  -- Sector restriction is non-zero.
  -- Hence μ IS an eigenvalue of the sector submatrix; sector min ≤ μ.
  have hsec_Herm := anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
    (Λ := Λ) (N := N) (M := M) hJ lam D
  have hne_bot : End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix J ((lam : ℂ)) ((D : ℂ)) N M))
      ((μ : ℝ) : ℂ) ≠ ⊥ := by
    intro hbot
    apply hvM_ne
    have hmem : magSectorRestriction (M := M) v ∈
        End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS_magSector_submatrix J ((lam : ℂ)) ((D : ℂ)) N M))
          ((μ : ℝ) : ℂ) := by
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hsec_eig
    rw [hbot] at hmem
    exact hmem
  have hHE : End.HasEigenvalue (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix J ((lam : ℂ)) ((D : ℂ)) N M))
      ((μ : ℝ) : ℂ) := hne_bot
  have h_mem_C : ((μ : ℝ) : ℂ) ∈ spectrum ℂ
      (anisotropicHeisenbergS_magSector_submatrix J ((lam : ℂ)) ((D : ℂ)) N M) := by
    rw [← Matrix.spectrum_toLin']
    exact hHE.mem_spectrum
  have h_mem_R : μ ∈ spectrum ℝ
      (anisotropicHeisenbergS_magSector_submatrix J ((lam : ℂ)) ((D : ℂ)) N M) := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]; exact h_mem_C
  rw [hsec_Herm.spectrum_real_eq_range_eigenvalues] at h_mem_R
  obtain ⟨i, hi⟩ := h_mem_R
  rw [← hi]
  exact hermitian_min_eigenvalue_le hsec_Herm i

end LatticeSystem.Quantum
