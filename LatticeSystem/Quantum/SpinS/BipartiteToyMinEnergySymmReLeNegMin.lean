import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReEqHalfImbalanceNormSq
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax

/-!
# Refined upper bound: `symm.re ≤ −min(|A|, |¬A|)·N`

PR #2878 gives the closed form

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = ‖biw‖²/2 − |Λ|²·N²/8 − min(|A|, |¬A|)·N`.

PR #2874 gives the upper bound `‖biw‖ ≤ |Λ|·N/2`, hence
`‖biw‖² ≤ |Λ|²·N²/4` and `‖biw‖²/2 ≤ |Λ|²·N²/8`. Therefore the
first two terms have non-positive sum and

  `(bipartiteToyMinEnergyPredictedSymm A N).re ≤ −min(|A|, |¬A|)·N`.

This refines PR #2844 (`(symm).re ≤ 0`) when `min > 0`; combined
with PR #2880 (`symm.re ≥ −|Λ|²·N²/8 − min·N`), we obtain the
tight `min`-aware sandwich

  `−|Λ|²·N²/8 − min·N ≤ symm.re ≤ −min·N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Refined upper bound on the symm-energy real part**:
`(bipartiteToyMinEnergyPredictedSymm A N).re ≤ −min(|A|, |¬A|)·N`.

Direct from PR #2878 closed form + PR #2874 imbalance-norm `m_max`
upper bound. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_le_neg_min :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ≤
      -(min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ)) := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq_half_imbalance_norm_sq_sub]
  -- ‖biw‖ ≤ |Λ|·N/2, hence ‖biw‖² ≤ |Λ|²·N²/4 and ‖biw‖²/2 ≤ |Λ|²·N²/8.
  have hbiw := bipartiteImbalanceWeight_norm_le_mMax (Λ := Λ) A N
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  have hLN_nn : 0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by positivity
  -- Square the inequality.
  have hsq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) :=
    mul_le_mul hbiw hbiw hbiw_nn hLN_nn
  nlinarith [hsq]

end LatticeSystem.Quantum
