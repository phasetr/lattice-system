import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# `magSectorEmbedding` of a sector ℂ-eigenvector is a full ℂ-eigenvector

(PR #3911, Issue #3739): ℂ-eigenvalue version of
`heisenbergHamiltonianS_mulVec_magSectorEmbedding`. The existing ℝ version
takes `μ : ℝ` and coerces to `(μ : ℂ)`; the ℂ version takes `μ : ℂ` directly.
Same proof structure — the eigenvalue appears only as a scalar multiplier.

Together with PR #3910 (the restriction direction), this gives the two-sided
ℂ-eigenvalue correspondence between the sector matrix and the full Hilbert
space, needed for the within-admissible Perron–Frobenius `finrank ≤ 1` input
in the SU(2) symmetric `finrank ≤ 1` capstone toward Tasaki §2.5 Theorem 2.4.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **ℂ-eigenvalue version**: the embedding of a sector ℂ-eigenvector is a full
Hilbert space ℂ-eigenvector at the same eigenvalue. -/
theorem heisenbergHamiltonianS_mulVec_magSectorEmbedding_complex
    (J : V → V → ℂ) {M : ℕ}
    (Φ : magConfigS V N M → ℂ)
    {μ : ℂ}
    (hΦ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ = μ • Φ) :
    (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      μ • (magSectorEmbedding Φ) := by
  classical
  funext σ
  by_cases h : magSumS σ = M
  · rw [heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype J Φ ⟨σ, h⟩]
    have hsec := congrFun hΦ ⟨σ, h⟩
    rw [hsec]
    change μ * Φ ⟨σ, h⟩ = (μ • magSectorEmbedding Φ) σ
    rw [Pi.smul_apply, magSectorEmbedding_apply_of_mem Φ h, smul_eq_mul]
  · have hLHS : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) σ = 0 := by
      change ∑ ρ, heisenbergHamiltonianS J N σ ρ * magSectorEmbedding Φ ρ = 0
      refine Finset.sum_eq_zero (fun ρ _ => ?_)
      by_cases hρ : magSumS ρ = M
      · have hne : magSumS ρ ≠ magSumS σ :=
          fun heq => h (heq.symm.trans hρ)
        rw [heisenbergHamiltonianS_apply_eq_zero_of_magSumS_ne (V := V) J N hne,
          zero_mul]
      · rw [magSectorEmbedding_apply_of_not_mem Φ hρ, mul_zero]
    rw [hLHS]
    change (0 : ℂ) = (μ • magSectorEmbedding Φ) σ
    rw [Pi.smul_apply, magSectorEmbedding_apply_of_not_mem Φ h, smul_zero]

end LatticeSystem.Quantum
