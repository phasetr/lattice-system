import LatticeSystem.Quantum.SpinS.BasisVecSOrthonormal
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Spanning and linear independence of `basisVecS`

The family `basisVecS : (V → Fin (N + 1)) → ((V → Fin (N + 1)) → ℂ)`
spans the full multi-site Hilbert space, and is linearly
independent (orthonormality from PR #914 implies LI). Together
these structural facts identify `basisVecS` as a basis of
`(V → Fin (N + 1)) → ℂ`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The `basisVecS` family spans the full multi-site Hilbert space. -/
theorem basisVecS_span_eq_top :
    Submodule.span ℂ (Set.range
      (fun σ : V → Fin (N + 1) =>
        (basisVecS σ : (V → Fin (N + 1)) → ℂ))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [fun_eq_sum_smul_basisVecS v]
  refine Submodule.sum_mem _ ?_
  intros σ _
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self σ)

/-- The `basisVecS` family is linearly independent. -/
theorem basisVecS_linearIndependent :
    LinearIndependent ℂ
      (fun σ : V → Fin (N + 1) =>
        (basisVecS σ : (V → Fin (N + 1)) → ℂ)) := by
  rw [linearIndependent_iff']
  intros s c hsum σ hσ
  -- Evaluate ∑ τ ∈ s, c τ • basisVecS τ at σ to extract c σ.
  have hσ_eval : (∑ τ ∈ s, c τ • basisVecS τ) σ = c σ := by
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single σ]
    · rw [Pi.smul_apply, basisVecS_self, smul_eq_mul, mul_one]
    · intros τ hτs hτne
      rw [Pi.smul_apply, basisVecS_of_ne (Ne.symm hτne), smul_eq_mul, mul_zero]
    · intro hσns
      exact (hσns hσ).elim
  have : (∑ τ ∈ s, c τ • basisVecS τ) σ = (0 : (V → Fin (N + 1)) → ℂ) σ := by
    rw [hsum]
  rw [hσ_eval] at this
  simpa using this

end LatticeSystem.Quantum
