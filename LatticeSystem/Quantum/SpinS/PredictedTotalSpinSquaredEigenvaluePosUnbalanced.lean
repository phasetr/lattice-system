import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNorm
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormPos

/-!
# Strict positivity of predicted `(Ŝ_tot)²` eigenvalue at strict unbalanced

PR #2930 gave the eigenvalue identification at `|¬A| ≤ |A|`:
`((s_A − s_B)·((s_A − s_B) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

At strict unbalanced `|¬A| < |A|` and `N ≥ 1`, `‖biw‖ > 0`
(PR #2867 `bipartiteImbalanceWeight_norm_pos_of_cardNotA_lt_cardA`),
so `‖biw‖·(‖biw‖+1) > 0`. Hence

  `0 < predicted (Ŝ_tot)² eigenvalue`
  at `|¬A| < |A|` and `N ≥ 1`.

The predicted GS has strictly positive `S_tot(S_tot+1)` at strict
unbalanced — i.e., a non-singlet ground state.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Strict positivity of predicted (Ŝ_tot)² eigenvalue** at
strict unbalanced (`|¬A| < |A|`, `N ≥ 1`). -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_pos_of_strict_unbalanced
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    0 <
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N (le_of_lt h)]
  -- ‖biw‖ > 0 at strict unbalanced.
  have hne : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
    ne_of_gt h
  have hbiw_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    bipartiteImbalanceWeight_norm_pos_of_card_ne A hN hne
  nlinarith [hbiw_pos]

end LatticeSystem.Quantum
