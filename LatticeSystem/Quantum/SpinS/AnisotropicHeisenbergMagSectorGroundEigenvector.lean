import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorEmbeddingLift
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorIsHermitianReal
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1

/-!
# Sector ground eigenvector existence for the anisotropic Hamiltonian

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Given the anisotropic sector submatrix `Ĥ_M(λ, D)` (Hermitian under real `(λ, D)`
and Hermitian `J`) on a non-empty `magConfigS Λ N M`, there exists a nonzero
sector vector `Φ` such that:
- The sector submatrix satisfies `Ĥ_M . Φ = (E_M : ℂ) . Φ` where
  `E_M = hermitianMinEigenvalue` of the sector submatrix.
- The lifted full vector `magSectorEmbedding Φ` is an eigenvector of the FULL
  anisotropic Hamiltonian `Ĥ(λ, D)` at the same `E_M`.
- `magSectorEmbedding Φ` lies in the magnetisation subspace `magSubspaceS Λ N (|V|·N/2 − M)`.

This packages the obligation (2) IVT crossing argument's sector→full bridge:
the per-sector min eigenvalue is realised by a full-Hilbert-space eigenvector
in the corresponding `Ŝ³_tot` eigenspace.

Combines:
- `exists_nonzero_eigenvector_hermitianMinEigenvalue` (PR #3962, sector-level).
- `anisotropicHeisenbergS_mulVec_magSectorEmbedding` (PR #3961, sector → full lift).
- `magSectorEmbedding_mem_magSubspaceS` (existing, magSubspaceS membership).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sector ground full-eigenvector existence**: for the anisotropic Hamiltonian
with real-coupling `J` and real `(λ, D)`, restricted to a non-empty magnetisation
sector `M`, there exists a nonzero sector vector `Φ` whose embedding is a
full-Hilbert-space eigenvector of `Ĥ(λ, D)` at the per-sector minimum eigenvalue
`E_M`. Additionally, the embedding lies in the `Ŝ³_tot` eigenspace
`magSubspaceS Λ N (|V|·N/2 − M)`. -/
theorem exists_sectorGround_full_eigenvector_anisotropicHeisenbergS
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y) (lam D : ℝ)
    (N M : ℕ) [Nonempty (magConfigS Λ N M)] :
    ∃ Φ : magConfigS Λ N M → ℂ, Φ ≠ 0 ∧
      (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec (magSectorEmbedding Φ) =
        ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ lam D) : ℝ) : ℂ) •
          magSectorEmbedding Φ ∧
      magSectorEmbedding Φ ∈ magSubspaceS Λ N
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
  classical
  -- Hermitian sector submatrix.
  have hHerm := anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
    (Λ := Λ) (N := N) (M := M) hJ lam D
  -- Sector eigenvector existence at min eigenvalue.
  obtain ⟨Φ, hΦ_ne, hΦ_eig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue hHerm
  refine ⟨Φ, hΦ_ne, ?_, ?_⟩
  · -- Lift via PR #3961.
    exact anisotropicHeisenbergS_mulVec_magSectorEmbedding J (lam : ℂ) (D : ℂ) Φ hΦ_eig
  · -- magSubspaceS membership from existing lemma.
    exact magSectorEmbedding_mem_magSubspaceS Φ

end LatticeSystem.Quantum
