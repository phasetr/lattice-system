import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# `magSectorRestriction` of a full ℂ-eigenvector is a sector ℂ-eigenvector

(PR #3910, Issue #3739): ℂ-eigenvalue version of
`heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen`.
The existing ℝ version takes `μ : ℝ` and coerces to `(μ : ℂ)`; the ℂ version
takes `μ : ℂ` directly. The proof is structurally identical — the eigenvalue
appears only as a scalar multiplier on `Ψ`.

This is needed for finrank-level eigenspace transfer in the SU(2) symmetric
`finrank ≤ 1` capstone toward Tasaki §2.5 Theorem 2.4.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **ℂ-eigenvalue version**: the sector restriction of a full Hilbert space
ℂ-eigenvector is a sector ℂ-eigenvector at the same eigenvalue. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen_complex
    (J : V → V → ℂ) {M : ℕ}
    {μ : ℂ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = μ • Ψ) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
      (magSectorRestriction (M := M) Ψ) =
      μ • magSectorRestriction (M := M) Ψ := by
  classical
  funext τ
  change (∑ τ', heisenbergHamiltonianSMatrixOnMagSector J N M τ τ' * Ψ τ'.1) =
    (μ • magSectorRestriction (M := M) Ψ) τ
  have hrhs : (μ • magSectorRestriction (M := M) Ψ) τ = μ * Ψ τ.1 := rfl
  rw [hrhs]
  have hsec : (∑ τ' : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M τ τ' * Ψ τ'.1) =
    ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
      (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ := by
    rw [Finset.sum_subtype (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
      (p := fun ρ => magSumS ρ = M)
      (fun ρ => by simp [Finset.mem_filter])
      (fun ρ => (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ)]
    rfl
  rw [hsec]
  have hfull : ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
      (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ =
    ∑ ρ : V → Fin (N + 1), (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ := by
    refine Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_
    intro ρ _ hne
    by_contra hρM
    apply hne
    have hmag_ne : magSumS ρ ≠ magSumS τ.1 := fun hEq => hρM (hEq.trans τ.2)
    rw [heisenbergHamiltonianS_apply_eq_zero_of_magSumS_ne (V := V) J N hmag_ne,
      zero_mul]
  rw [hfull]
  change (heisenbergHamiltonianS J N).mulVec Ψ τ.1 = _
  rw [hΨ]
  rfl

end LatticeSystem.Quantum
