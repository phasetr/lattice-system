import LatticeSystem.Quantum.SpinS.MinNEqHalfCardTimesNMinusImbalanceNorm

/-!
# Strict imbalance-norm `m_max` upper bound at non-degenerate

PR #2874 gave the weak bound `‖biw‖ ≤ |Λ|·N/2 = m_max`. In the
**non-degenerate case** (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`) the
inequality is **strict**:

  `‖bipartiteImbalanceWeight A N‖ < |Λ|·N/2`.

Proof: from the identity `min·N = |Λ|·N/2 − ‖biw‖` (PR #2887),
strictness amounts to `min·N > 0`, which is just
`0 < min(|A|, |¬A|) · N` at non-degeneracy.

Saturated at `min = 0`, i.e., `|A| = 0 ∨ |¬A| = 0` (the saturated
edge configurations). At those degenerate configurations,
`‖biw‖ = |Λ|·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict `m_max` upper bound** (non-degenerate case):
`‖bipartiteImbalanceWeight A N‖ < |Λ|·N/2` when `|A| ≥ 1`,
`|¬A| ≥ 1`, `N ≥ 1`. -/
theorem bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  -- Use the identity min·N = |Λ|·N/2 - ‖biw‖.
  have hidentity :=
    min_cardA_cardNotA_mul_N_eq_half_card_times_N_sub_imbalance_norm
      (Λ := Λ) A N
  -- min > 0 at non-degenerate, so min·N > 0.
  have hA_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    by exact_mod_cast hA
  have hAc_pos : (0 : ℝ) <
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    by exact_mod_cast hAc
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmin_pos :
      0 < min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    lt_min hA_pos hAc_pos
  have hmin_N_pos : 0 <
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        (N : ℝ) := mul_pos hmin_pos hN_pos
  linarith

end LatticeSystem.Quantum
