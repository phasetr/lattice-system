import LatticeSystem.Quantum.SpinS.CorrelationOffDiagonal
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace

/-!
# Off-diagonal correlation sum on the saturated-ferromagnet states

For the saturated-ferromagnet states `|σ_⊤⟩` and `|σ_⊥⟩`, the sum
of off-diagonal two-site correlations evaluates explicitly to

  `∑_{x ≠ y} ⟨|σ_⊤⟩, Ŝ_x · Ŝ_y · |σ_⊤⟩⟩
    = m_max(m_max + 1) − |V|·S(S+1)
    = (|V|·N/2)·(|V|·N/2 + 1) − |V|·N(N+2)/4
    = N²·|V|·(|V| − 1)/4
    = |V|·S²·(|V| − 1)`.

For `|V| = 1` (single site): off-diag sum = 0 (no off-diagonal
terms, as expected). For `|V| = 2` spin-`1/2`: off-diag = 1/2,
matching the standard two-site triplet correlation.

Direct application of PR #933 with the saturated-FM Casimir
eigenvalue and normalization (#913).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The off-diagonal correlation sum on `|σ_⊤⟩` evaluates to
`(|V|·N/2)·(|V|·N/2 + 1) − |V|·N(N+2)/4`. -/
theorem allAlignedStateS_zero_correlation_offdiag_sum [Nonempty V] :
    ∑ x : V, ∑ y ∈ (Finset.univ.erase x),
        dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
          ((spinSDot x y N).mulVec
            (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) -
      (Fintype.card V : ℂ) * ((N : ℂ) * (N + 2) / 4) := by
  -- |σ_⊤⟩ is a Ŝ_tot² eigenvector at m_max(m_max+1) (PR #882, k=0).
  have h_eig : (totalSpinSSquared V N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        (allAlignedStateS V N (0 : Fin (N + 1))) := by
    have h := totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
      (V := V) (N := N) 0
    simp only [pow_zero, Matrix.one_mulVec] at h
    exact h
  rw [totalSpinSSquared_eigenvector_correlation_offdiag_sum h_eig]
  rw [allAlignedStateS_inner_self, mul_one]

/-- Symmetric off-diagonal correlation sum on `|σ_⊥⟩`. -/
theorem allAlignedStateS_last_correlation_offdiag_sum [Nonempty V] :
    ∑ x : V, ∑ y ∈ (Finset.univ.erase x),
        dotProduct (star (allAlignedStateS V N (Fin.last N)))
          ((spinSDot x y N).mulVec
            (allAlignedStateS V N (Fin.last N))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1) -
      (Fintype.card V : ℂ) * ((N : ℂ) * (N + 2) / 4) := by
  have h_eig : (totalSpinSSquared V N).mulVec
      (allAlignedStateS V N (Fin.last N)) =
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        (allAlignedStateS V N (Fin.last N)) := by
    have h := totalSpinSSquared_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
      (V := V) (N := N) 0
    simp only [pow_zero, Matrix.one_mulVec] at h
    exact h
  rw [totalSpinSSquared_eigenvector_correlation_offdiag_sum h_eig]
  rw [allAlignedStateS_inner_self, mul_one]

end LatticeSystem.Quantum
