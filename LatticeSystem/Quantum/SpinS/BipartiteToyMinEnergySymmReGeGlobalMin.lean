import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReGeNegBalanced
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Global lower bound: `symm.re ≥ −|Λ|²·N²/8 − |Λ|·N/2`

PR #2880 established the cardinality-dependent lower bound

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     ≥ −|Λ|²·N²/8 − min(|A|, |¬A|)·N`.

Combining with the bound `min(|A|, |¬A|) ≤ |Λ|/2` (from
`min ≤ (|A| + |¬A|)/2 = |Λ|/2`, PR #2870), we get the
**configuration-independent global lower bound**

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     ≥ −|Λ|²·N²/8 − |Λ|·N/2`.

This bound is saturated exactly at balanced sublattices
(`|A| = |¬A|`, PR #2881), so balanced configurations realise the
global minimum of the symm-predicted energy real part among all
bipartitions of `Λ` of fixed cardinality.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Global lower bound on the symm-energy real part**:
`−|Λ|²·N²/8 − |Λ|·N/2 ≤ (bipartiteToyMinEnergyPredictedSymm A N).re`.

Configuration-independent bound combining PR #2880 (lower bound)
with PR #2870 (cardinality sum). Saturated at balanced sublattices
(PR #2881). -/
theorem bipartiteToyMinEnergyPredictedSymm_re_ge_global_min_bound :
    -((Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 8) -
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 ≤
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  have hlower :=
    bipartiteToyMinEnergyPredictedSymm_re_ge_neg_balanced_bound A N
  have hsum := cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hsum_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by exact_mod_cast hsum
  have ha_nn : 0 ≤ ((Finset.univ.filter
    (fun x : Λ => A x = true)).card : ℝ) := Nat.cast_nonneg _
  have hb_nn : 0 ≤ ((Finset.univ.filter
    (fun x : Λ => (! A x) = true)).card : ℝ) := Nat.cast_nonneg _
  have hN_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  -- min ≤ (a+b)/2 = |Λ|/2.
  have hmin_le :
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
        (Fintype.card Λ : ℝ) / 2 := by
    have hmin_le_a := min_le_left
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
    have hmin_le_b := min_le_right
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
    linarith
  -- −min·N ≥ −|Λ|·N/2.
  have hmin_N_le : min ((Finset.univ.filter
        (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      (N : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_right hmin_le hN_nn
    linarith
  linarith

end LatticeSystem.Quantum
