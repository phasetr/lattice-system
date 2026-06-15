import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSectorZero
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuity
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Anisotropic sector inverse lift: full → sector eigenvector restriction

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

The anisotropic analog of
`heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen`
(in `MagSectorEmbedding.lean`): a full-Hilbert-space eigenvector `Ψ` of
`Ĥ(λ, D)` at energy `μ` restricts to a sector-`M` eigenvector of the sector
submatrix `Ĥ_M(λ, D)` at the same `μ`.

Proof: the U(1) invariance (`anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne`,
PR #3898) lets us drop off-sector terms in the `mulVec` expansion.

Used by the first-crossing argument's hard direction (global min Ĥ ≥ min over
sector mins): a non-zero sector projection of a full GS eigenvector gives a
sector eigenvector at the same energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Anisotropic sector inverse lift**: a full-Ĥ eigenvector `Ψ` at energy `μ`
restricts to a sector-`M` eigenvector of `Ĥ_M(λ, D)` at the same `μ`.

Note: when the sector is empty (i.e., `magConfigS Λ N M` is empty), the
conclusion holds vacuously since both sides are zero functions on an empty domain. -/
theorem anisotropicHeisenbergS_magSector_submatrix_mulVec_magSectorRestriction_of_full_eigen
    (J : Λ → Λ → ℂ) (lam D : ℂ) {M : ℕ}
    {μ : ℂ} {Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΨ : (anisotropicHeisenbergS J lam D N).mulVec Ψ = μ • Ψ) :
    (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M).mulVec
      (magSectorRestriction (M := M) Ψ) =
      μ • magSectorRestriction (M := M) Ψ := by
  classical
  funext τ
  -- Goal: (Ĥ_M).mulVec (restrict Ψ) τ = (μ • restrict Ψ) τ.
  -- (μ • restrict Ψ) τ = μ * Ψ τ.1.
  have hrhs : (μ • magSectorRestriction (M := M) Ψ) τ = μ * Ψ τ.1 := rfl
  rw [hrhs]
  -- LHS: (Ĥ_M).mulVec (restrict Ψ) τ = ∑ τ' : magConfigS, Ĥ_M τ τ' * (restrict Ψ) τ'.
  --     = ∑ τ' : magConfigS, Ĥ τ.1 τ'.1 * Ψ τ'.1.
  -- Convert subtype sum to filter sum.
  change ∑ τ' : magConfigS Λ N M,
      anisotropicHeisenbergS_magSector_submatrix J lam D N M τ τ' *
        magSectorRestriction (M := M) Ψ τ' = μ * Ψ τ.1
  have hsec : (∑ τ' : magConfigS Λ N M,
      anisotropicHeisenbergS_magSector_submatrix J lam D N M τ τ' *
        magSectorRestriction (M := M) Ψ τ') =
    ∑ ρ ∈ Finset.univ.filter (fun ρ : Λ → Fin (N + 1) => magSumS ρ = M),
      (anisotropicHeisenbergS J lam D N) τ.1 ρ * Ψ ρ := by
    rw [Finset.sum_subtype
      (Finset.univ.filter (fun ρ : Λ → Fin (N + 1) => magSumS ρ = M))
      (p := fun ρ => magSumS ρ = M)
      (fun ρ => by simp [Finset.mem_filter])
      (fun ρ => (anisotropicHeisenbergS J lam D N) τ.1 ρ * Ψ ρ)]
    refine Finset.sum_congr rfl (fun ρ' _ => ?_)
    unfold anisotropicHeisenbergS_magSector_submatrix
    rw [Matrix.submatrix_apply]; rfl
  rw [hsec]
  -- Extend filter sum to full sum (added terms are zero by U(1) sector-crossing vanishing).
  have hfull : ∑ ρ ∈ Finset.univ.filter (fun ρ : Λ → Fin (N + 1) => magSumS ρ = M),
      (anisotropicHeisenbergS J lam D N) τ.1 ρ * Ψ ρ =
    ∑ ρ : Λ → Fin (N + 1), (anisotropicHeisenbergS J lam D N) τ.1 ρ * Ψ ρ := by
    refine Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_
    intro ρ _ hne
    by_contra hρM
    apply hne
    have hmag_ne : magSumS τ.1 ≠ magSumS ρ :=
      fun heq => hρM (heq.symm.trans τ.2)
    rw [anisotropicHeisenbergS_apply_eq_zero_of_magSumS_ne J lam D hmag_ne, zero_mul]
  rw [hfull]
  -- This is (Ĥ).mulVec Ψ τ.1 = (μ • Ψ) τ.1.
  change (anisotropicHeisenbergS J lam D N).mulVec Ψ τ.1 = _
  rw [hΨ]
  rfl

end LatticeSystem.Quantum
