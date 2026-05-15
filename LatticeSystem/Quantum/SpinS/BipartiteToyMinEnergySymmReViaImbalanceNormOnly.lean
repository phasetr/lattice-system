import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReEqHalfImbalanceNormSq
import LatticeSystem.Quantum.SpinS.MinNEqHalfCardTimesNMinusImbalanceNorm

/-!
# `symm.re` parameterized by `‖biw‖` alone

PR #2878 gave the closed form

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = ‖biw‖²/2 − |Λ|²·N²/8 − min(|A|, |¬A|)·N`.

PR #2887 established the linear identity

  `min(|A|, |¬A|)·N = |Λ|·N/2 − ‖biw‖`.

Substituting eliminates the `min`-dependence completely:

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = ‖biw‖²/2 + ‖biw‖ − |Λ|²·N²/8 − |Λ|·N/2`.

The predicted symmetric ground-state energy is therefore a
**univariate quadratic function** of the imbalance norm `‖biw‖`,
parameterised by `|Λ|` and `N`. This is the natural Tasaki §2.5
Theorem 2.3 (γ-4) viewpoint: the energy depends only on the
predicted total-spin magnitude (and the fixed lattice
cardinality).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Univariate `‖biw‖`-parameterisation of the symm-energy real
part**:
`(bipartiteToyMinEnergyPredictedSymm A N).re
   = ‖biw‖²/2 + ‖biw‖ − |Λ|²·N²/8 − |Λ|·N/2`.

Direct from PR #2878 + PR #2887. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_only :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ / 2 +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
            ((N : ℝ) * (N : ℝ)) / 8 -
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq_half_imbalance_norm_sq_sub]
  rw [min_cardA_cardNotA_mul_N_eq_half_card_times_N_sub_imbalance_norm]
  ring

end LatticeSystem.Quantum
