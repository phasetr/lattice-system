import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredVsPredictedGap

/-!
# Néel-vs-predicted-(Ŝ_tot)² gap = 0 ↔ saturated edge at `N ≥ 1`

PR #2901 established the gap equality
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖) = min(|A|, |¬A|) · N`.

At `N ≥ 1`, the gap vanishes iff `min(|A|, |¬A|) · N = 0`, iff
`min(|A|, |¬A|) = 0`, iff `|A| = 0 ∨ |¬A| = 0` (saturated edge).

  `gap = 0 ↔ |A| = 0 ∨ |¬A| = 0`   at `N ≥ 1`.

This characterises exactly which configurations have the Néel
state's `(Ŝ_tot)²` expectation matching the predicted GS
eigenvalue.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Gap iff characterisation**: at `N ≥ 1`,
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖) = 0 ↔
|A| = 0 ∨ |¬A| = 0`. -/
theorem neelStateOfS_totalSpinSSquared_vs_predicted_gap_eq_zero_iff_saturated
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re -
        (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
            ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  rw [neelStateOfS_totalSpinSSquared_expectation_re_sub_predicted_eq_min_N]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro h
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
    -- h : min ((|A|, |¬A|)) * N = 0
    have hmin_eq_zero :
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
      have hmul_zero := h
      have := mul_eq_zero.mp hmul_zero
      rcases this with h | h
      · exact h
      · exact absurd h hN_ne
    rcases le_total
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) with hab | hba
    · left
      rw [min_eq_left hab] at hmin_eq_zero
      exact_mod_cast hmin_eq_zero
    · right
      rw [min_eq_right hba] at hmin_eq_zero
      exact_mod_cast hmin_eq_zero
  · intro h
    rcases h with hA_zero | hAc_zero
    · have hA_real :
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hA_zero
      have hA_nn : 0 ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
        Nat.cast_nonneg _
      have hAc_nn : 0 ≤
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
        Nat.cast_nonneg _
      have hmin_zero :
          min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hA_real]; exact min_eq_left hAc_nn
      rw [hmin_zero]; ring
    · have hAc_real :
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hAc_zero
      have hA_nn : 0 ≤
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
        Nat.cast_nonneg _
      have hmin_zero :
          min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        rw [hAc_real]; exact min_eq_right hA_nn
      rw [hmin_zero]; ring

end LatticeSystem.Quantum
