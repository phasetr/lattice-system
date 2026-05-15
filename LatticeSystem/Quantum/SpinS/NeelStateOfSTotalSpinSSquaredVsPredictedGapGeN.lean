import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredVsPredictedGap

/-!
# Quantitative Néel-vs-predicted-(Ŝ_tot)² gap ≥ N at non-degenerate

PR #2901 established the gap equality
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖) = min(|A|, |¬A|)·N`.

In the **non-degenerate case** (`|A| ≥ 1`, `|¬A| ≥ 1`), `min ≥ 1`,
hence the quantitative lower bound

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖) ≥ N`.

Parallel of the energy quantitative gap (PR #2899) for the
`(Ŝ_tot)²` Casimir: at non-degenerate, Néel state's `(Ŝ_tot)²`
expectation is at least `N` above the predicted GS eigenvalue.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Quantitative Néel-vs-predicted (Ŝ_tot)² gap lower bound**:
at `|A| ≥ 1` and `|¬A| ≥ 1`,
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re − (‖biw‖² + ‖biw‖) ≥ N`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_sub_predicted_ge_N_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    (N : ℝ) ≤
      (dotProduct (star (neelStateOfS A N))
          ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re -
        (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
            ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) := by
  have hgap :=
    neelStateOfS_totalSpinSSquared_expectation_re_sub_predicted_eq_min_N
      (Λ := Λ) A N
  have hA_pos : (1 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
    exact_mod_cast hA
  have hAc_pos : (1 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast hAc
  have hN_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hmin_ge_one :
      (1 : ℝ) ≤
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    le_min hA_pos hAc_pos
  nlinarith [hgap, hmin_ge_one, hN_nn]

end LatticeSystem.Quantum
