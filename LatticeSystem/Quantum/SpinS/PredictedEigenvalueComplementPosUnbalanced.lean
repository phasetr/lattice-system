import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNormComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormPos

/-!
# Strict positivity of complement predicted `(Ŝ_tot)²` eigenvalue at strict unbalanced

PR #2931 gave the complement eigenvalue identification at
`|A| ≤ |¬A|`:
`((s_B − s_A)·((s_B − s_A) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

At strict unbalanced `|A| < |¬A|` and `N ≥ 1`, `‖biw‖ > 0`, so
`‖biw‖·(‖biw‖+1) > 0`. Hence

  `0 < complement predicted (Ŝ_tot)² eigenvalue`
  at `|A| < |¬A|` and `N ≥ 1`.

Mirror of PR #2937. The complement predicted GS has strictly positive
`S_tot(S_tot+1)` at strict unbalanced.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Strict positivity of complement predicted (Ŝ_tot)² eigenvalue**
at strict unbalanced (`|A| < |¬A|`, `N ≥ 1`). Mirror of PR #2937. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_pos_of_strict_unbalanced
    (A : Λ → Bool) {N : ℕ} (hN : 1 ≤ N)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card <
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    0 <
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N (le_of_lt h)]
  -- ‖biw‖ > 0 at strict unbalanced.
  have hne : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
    ne_of_lt h
  have hbiw_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    bipartiteImbalanceWeight_norm_pos_of_card_ne A hN hne
  nlinarith [hbiw_pos]

end LatticeSystem.Quantum
