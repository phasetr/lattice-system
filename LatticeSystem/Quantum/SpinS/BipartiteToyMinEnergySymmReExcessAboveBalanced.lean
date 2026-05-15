import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormOnly

/-!
# Excess of symm-energy real part above the balanced minimum

PR #2888 gave the univariate form
`(symm).re = ‖biw‖²/2 + ‖biw‖ − |Λ|²·N²/8 − |Λ|·N/2`.

The balanced minimum (at `‖biw‖ = 0`) is `−|Λ|²·N²/8 − |Λ|·N/2`
(PR #2881). The excess above this minimum is therefore

  `(symm).re + |Λ|²·N²/8 + |Λ|·N/2 = ‖biw‖²/2 + ‖biw‖ = ‖biw‖·(‖biw‖+2)/2`.

This identifies the "energy cost" of unbalanced configurations
above the balanced singlet-prediction minimum as a quadratic
function of the predicted spin magnitude `‖biw‖`. Vanishes at
balanced (`‖biw‖ = 0`) and equals `m_max·(m_max+2)/2` at saturated
(`‖biw‖ = m_max`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Excess of symm-energy above balanced minimum**:
`(symm).re + |Λ|²·N²/8 + |Λ|·N/2 = ‖biw‖²/2 + ‖biw‖`.

The bipartition-dependent excess equals `‖biw‖·(‖biw‖+2)/2`,
vanishing at balanced and reaching `m_max·(m_max+2)/2` at
saturated. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_add_balanced_min_eq_imbalance_norm_quad :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re +
        ((Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 8) +
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ / 2 +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only]
  ring

end LatticeSystem.Quantum
