import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredVsPredictedGap

/-!
# Strict positive Néel-vs-predicted-(Ŝ_tot)² gap at non-degenerate

PR #2901 established the (Ŝ_tot)² gap equality

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖)
     = min(|A|, |¬A|)·N`.

In the **non-degenerate case** (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`),
`min(|A|, |¬A|)·N > 0`, hence the strict inequality

  `‖biw‖² + ‖biw‖ < (<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re`.

The Néel state's `(Ŝ_tot)²` expectation is **strictly above** the
predicted ground-state eigenvalue `‖biw‖·(‖biw‖+1)` at
non-degenerate configurations, demonstrating that the Néel state
spans multiple `S_tot` sectors (not the GS).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict positive Néel-vs-predicted (Ŝ_tot)² gap** in the
non-degenerate case: `‖biw‖² + ‖biw‖ < (<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re`
when `|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_gt_predicted_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ <
      (dotProduct (star (neelStateOfS A N))
          ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re := by
  have hgap :=
    neelStateOfS_totalSpinSSquared_expectation_re_sub_predicted_eq_min_N
      (Λ := Λ) A N
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
  nlinarith [hgap, hmin_pos, hN_pos]

end LatticeSystem.Quantum
