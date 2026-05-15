import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormOnly

/-!
# Strict global lower bound at unbalanced configurations

PR #2882 gave the configuration-independent global lower bound

  `−|Λ|²·N²/8 − |Λ|·N/2 ≤ (symm).re`.

The bound is saturated only at balanced sublattices (`‖biw‖ = 0`,
PR #2881). At **strictly unbalanced** configurations (`‖biw‖ > 0`),
the inequality is **strict**:

  `−|Λ|²·N²/8 − |Λ|·N/2 < (symm).re`.

Proof: from PR #2888 univariate form
`(symm).re = ‖biw‖²/2 + ‖biw‖ + (constants)`, strictness reduces
to `‖biw‖²/2 + ‖biw‖ > 0`, which holds for `‖biw‖ > 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict global lower bound at unbalanced configurations**:
`−|Λ|²·N²/8 − |Λ|·N/2 < (bipartiteToyMinEnergyPredictedSymm A N).re`
when `‖bipartiteImbalanceWeight A N‖ > 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_gt_global_min_bound_of_unbalanced
    (A : Λ → Bool) (N : ℕ)
    (h : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) :
    -((Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 8) -
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 <
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only]
  nlinarith [h]

end LatticeSystem.Quantum
