import LatticeSystem.Quantum.SpinS.CorrelationEigenvector
import LatticeSystem.Quantum.SpinS.SingleSiteCasimirExpectation

/-!
# Off-diagonal two-site correlation sum on `Ŝ_tot²`-eigenvectors

For a `Ŝ_tot²`-eigenvector `Φ` at eigenvalue `λ`, the off-diagonal
two-site correlation sum equals
`(λ − |V|·N(N+2)/4) · ⟨Φ, Φ⟩`:

  `∑_{x ≠ y} ⟨Φ, Ŝ_x · Ŝ_y · Φ⟩ = (λ − |V|·S(S+1)) · ⟨Φ, Φ⟩`.

Direct derivation: subtract diagonal `∑_x ⟨Φ, Ŝ_x · Ŝ_x · Φ⟩ =
|V|·S(S+1) · ⟨Φ, Φ⟩` (from PR #920) from full sum `λ · ⟨Φ, Φ⟩`
(PR #931).

Specialisations:
- Singlet (`λ = 0`): off-diag sum = `−|V|·S(S+1) · ⟨Φ, Φ⟩`.
- Saturated FM (`λ = m_max(m_max+1)`): off-diag sum =
  `(m_max(m_max+1) − |V|·S(S+1)) · ⟨Φ, Φ⟩
  = |V|·S² · (|V| − 1) · ⟨Φ, Φ⟩`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The diagonal correlation sum equals `|V|·S(S+1) · ⟨Φ, Φ⟩` for
any state `Φ`. Universal — does not depend on `Φ`. -/
theorem correlation_diag_sum_eq_full_state_norm
    (Φ : (V → Fin (N + 1)) → ℂ) :
    ∑ x : V, dotProduct (star Φ) ((spinSDot x x N).mulVec Φ) =
      (Fintype.card V : ℂ) * ((N : ℂ) * (N + 2) / 4) *
        dotProduct (star Φ) Φ := by
  have h_each : ∀ x : V,
      dotProduct (star Φ) ((spinSDot x x N).mulVec Φ) =
        ((N : ℂ) * (N + 2) / 4) * dotProduct (star Φ) Φ := by
    intro x
    exact spinSDot_self_expectation x Φ
  rw [Finset.sum_congr rfl (fun x _ => h_each x)]
  rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- For a `Ŝ_tot²`-eigenvector at eigenvalue `lam`, the
off-diagonal correlation sum equals
`(lam − |V|·N(N+2)/4) · ⟨Φ, Φ⟩`. -/
theorem totalSpinSSquared_eigenvector_correlation_offdiag_sum
    {lam : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared V N).mulVec Φ = lam • Φ) :
    ∑ x : V, ∑ y ∈ (Finset.univ.erase x),
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) =
      (lam - (Fintype.card V : ℂ) * ((N : ℂ) * (N + 2) / 4)) *
        dotProduct (star Φ) Φ := by
  -- ∑_{x≠y} = ∑_{x,y} - ∑_x (diag x x) = lam · ⟨Φ,Φ⟩ - |V| S(S+1) · ⟨Φ,Φ⟩.
  have h_full := totalSpinSSquared_eigenvector_correlation_full_sum hΦ
  have h_diag := correlation_diag_sum_eq_full_state_norm Φ
  have h_split : ∑ x : V, ∑ y : V,
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) =
      ∑ x : V, ∑ y ∈ (Finset.univ.erase x),
        dotProduct (star Φ) ((spinSDot x y N).mulVec Φ) +
      ∑ x : V, dotProduct (star Φ) ((spinSDot x x N).mulVec Φ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  rw [h_split] at h_full
  rw [h_diag] at h_full
  linear_combination h_full

end LatticeSystem.Quantum
