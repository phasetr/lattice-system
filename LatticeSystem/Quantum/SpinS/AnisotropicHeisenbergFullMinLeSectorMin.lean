import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorGroundEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue

/-!
# `hermitianMinEigenvalue Ĥ ≤ hermitianMinEigenvalue Ĥ_M` (sector min upper-bounds global min)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

For real-coupling `J` and real `(λ, D)`, the sector-`M` min eigenvalue
`hermitianMinEigenvalue Ĥ_M(λ, D)` is `≥` the full `Ĥ` global min eigenvalue
(equivalently, the global min is `≤` each sector min). This is the easy
direction of the global-min-over-sector-mins identity, sufficient for the
first-crossing argument's `0 ∈ balancedGSSet` step under the strict gap axiom.

Proof: PR #3963 produces a sector ground full-eigenvector at energy
`hermitianMinEigenvalue Ĥ_M`, so this is an eigenvalue of Ĥ;
`hermitian_min_eigenvalue_le` then gives the bound.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Global Ĥ min ≤ each sector min**: for real-coupling `J` and real `(λ, D)`,
the sector-`M` min eigenvalue is `≥` the full `Ĥ` global min. -/
theorem hermitianMinEigenvalue_anisotropicHeisenbergS_full_le_sector
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) (lam D : ℝ) [Nonempty (magConfigS Λ N M)]
    [Nonempty (Λ → Fin (N + 1))] :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D) ≤
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ lam D) := by
  classical
  -- Get a sector ground full-eigenvector at the sector min.
  obtain ⟨Φ, hΦ_ne, hΦ_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ lam D N M
  -- Φ_embed is a full-Ĥ eigenvector at sector min; hence sector min ∈ spectrum.
  set μ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M) hJ lam D) with hμ_def
  set Ψ : (Λ → Fin (N + 1)) → ℂ := magSectorEmbedding Φ with hΨ_def
  have hΨ_ne : Ψ ≠ 0 := by
    intro h
    apply hΦ_ne
    funext τ
    have := congrFun h τ.1
    rwa [hΨ_def, magSectorEmbedding_apply_subtype Φ τ] at this
  -- Eigenspace at (μ : ℂ) is non-trivial.
  have hΨ_mem : Ψ ∈ Module.End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N)) ((μ : ℝ) : ℂ) := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ_eig
  have hne_bot : Module.End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N)) ((μ : ℝ) : ℂ) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hΨ_mem
    exact hΨ_ne hΨ_mem
  -- HasEigenvalue → mem_spectrum.
  have hHE : Module.End.HasEigenvalue (Matrix.toLin'
      (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N)) ((μ : ℝ) : ℂ) := hne_bot
  have hHerm := anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D
  -- Convert to real-spectrum membership.
  have h_mem_C : ((μ : ℝ) : ℂ) ∈ spectrum ℂ
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N) := by
    rw [← Matrix.spectrum_toLin']
    exact hHE.mem_spectrum
  have h_mem_R : μ ∈ spectrum ℝ
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N) := by
    rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ)]; exact h_mem_C
  rw [hHerm.spectrum_real_eq_range_eigenvalues] at h_mem_R
  obtain ⟨i, hi⟩ := h_mem_R
  rw [← hi]
  exact hermitian_min_eigenvalue_le hHerm i

end LatticeSystem.Quantum
