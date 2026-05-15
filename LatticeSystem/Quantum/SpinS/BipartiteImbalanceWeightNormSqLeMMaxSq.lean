import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax

/-!
# Squared `m_max` upper bound: `‖biw‖² ≤ |Λ|²·N²/4`

PR #2874 gave the linear bound `‖biw‖ ≤ |Λ|·N/2 = m_max`.
Squaring (both sides non-negative):

  `‖bipartiteImbalanceWeight A N‖² ≤ |Λ|²·N²/4 = m_max²`.

This is the squared form, directly useful when combined with the
Néel-state `(Ŝ_tot^(3))²` expectation
`<(Ŝ_tot^(3))²>_Néel.re = ‖biw‖²` (PR #2904) to get
`<(Ŝ_tot^(3))²>_Néel.re ≤ m_max²` (non-strict version of PR #2909).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Squared `m_max` upper bound**:
`‖bipartiteImbalanceWeight A N‖² ≤ |Λ|²·N²/4`. -/
theorem bipartiteImbalanceWeight_norm_sq_le_mMax_sq :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
        ((N : ℝ) * (N : ℝ)) / 4 := by
  have hbiw := bipartiteImbalanceWeight_norm_le_mMax (Λ := Λ) A N
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    norm_nonneg _
  have hLN_nn : 0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by positivity
  have hsq := mul_le_mul hbiw hbiw hbiw_nn hLN_nn
  nlinarith [hsq]

end LatticeSystem.Quantum
