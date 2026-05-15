import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReEqHalfImbalanceNormSq

/-!
# Lower bound: `symm.re ≥ −|Λ|²·N²/8 − min·N`

PR #2878 established the explicit closed form

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = ‖bipartiteImbalanceWeight A N‖² / 2 − |Λ|²·N²/8 − min(|A|, |¬A|)·N`.

Since `‖biw‖² ≥ 0`, dropping the `‖biw‖²/2` non-negative summand
gives the **lower bound**

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     ≥ −|Λ|²·N²/8 − min(|A|, |¬A|)·N`.

Combined with PR #2844's upper bound `(symm).re ≤ 0`, this is a
sandwich. Equality in the lower bound is achieved iff
`‖biw‖ = 0`; for `N ≥ 1` this characterises balanced sublattices
(`|A| = |¬A|`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Lower bound on the predicted symm-energy real part**:
`(bipartiteToyMinEnergyPredictedSymm A N).re ≥ −|Λ|²·N²/8 − min(|A|, |¬A|)·N`.

Direct from PR #2878's explicit closed form by dropping the non-negative
`‖biw‖²/2` term. Equality at balanced sublattices. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_ge_neg_balanced_bound :
    -((Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 8) -
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) ≤
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq_half_imbalance_norm_sq_sub]
  have hnn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  linarith

end LatticeSystem.Quantum
