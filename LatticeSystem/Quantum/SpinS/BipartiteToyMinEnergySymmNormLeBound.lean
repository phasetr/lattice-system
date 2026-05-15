import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNorm
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Upper bound: `‖bipartiteToyMinEnergyPredictedSymm A N‖ ≤ |Λ|²·N²/8 + |Λ|·N/2`

PR #2848 gave `‖symm‖ = |A|·|¬A|·N²/2 + min(|A|, |¬A|)·N`.

By AM-GM, `|A|·|¬A| ≤ ((|A|+|¬A|)/2)² = |Λ|²/4`, and
`min(|A|, |¬A|) ≤ |Λ|/2`. Hence

  `‖bipartiteToyMinEnergyPredictedSymm A N‖
     ≤ |Λ|²·N²/8 + |Λ|·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Symm-energy norm upper bound**:
`‖bipartiteToyMinEnergyPredictedSymm A N‖ ≤ |Λ|²·N²/8 + |Λ|·N/2`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_le_balanced_bound :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ ≤
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) * ((N : ℝ) * (N : ℝ)) / 8 +
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [bipartiteToyMinEnergyPredictedSymm_norm_eq]
  have hsum := cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hsum_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by exact_mod_cast hsum
  set a : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set b : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  set L : ℝ := (Fintype.card Λ : ℝ)
  have hab : a + b = L := hsum_real
  have ha_nn : 0 ≤ a := Nat.cast_nonneg _
  have hb_nn : 0 ≤ b := Nat.cast_nonneg _
  have hN_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  -- AM-GM: a·b ≤ ((a+b)/2)² = L²/4.
  have hAMGM : a * b ≤ L * L / 4 := by
    have h := sq_nonneg (a - b)
    nlinarith [hab]
  -- min ≤ (a+b)/2 = L/2.
  have hmin : min a b ≤ L / 2 := by
    have hmin_le_a : min a b ≤ a := min_le_left a b
    have hmin_le_b : min a b ≤ b := min_le_right a b
    linarith
  have hmin_nn : 0 ≤ min a b := le_min ha_nn hb_nn
  -- Now combine.
  have h1 : a * b * ((N : ℝ) * (N : ℝ)) / 2 ≤
      L * L * ((N : ℝ) * (N : ℝ)) / 8 := by
    have hNsq_nn : 0 ≤ (N : ℝ) * (N : ℝ) := by positivity
    nlinarith [hAMGM, hNsq_nn]
  have h2 : min a b * (N : ℝ) ≤ L / 2 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hmin hN_nn
  linarith

end LatticeSystem.Quantum
