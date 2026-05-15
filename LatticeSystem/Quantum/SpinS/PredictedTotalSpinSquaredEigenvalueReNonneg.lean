import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNorm

/-!
# Non-negativity of predicted `(Ŝ_tot)²` eigenvalue at proper orientation

PR #2930 identified the predicted `(Ŝ_tot)²` eigenvalue with
`‖biw‖·(‖biw‖+1)` at `|¬A| ≤ |A|`. Since `‖biw‖ ≥ 0`, this is
non-negative:

  `((s_A − s_B)·((s_A − s_B) + 1)).re ≥ 0`   at `|¬A| ≤ |A|`.

The predicted GS Casimir eigenvalue is physical (non-negative)
exactly under the proper orientation `|¬A| ≤ |A|`. The complement
orientation may give a "formally negative" eigenvalue which
indicates the wrong choice of orientation for the predicted GS.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Non-negativity of predicted `(Ŝ_tot)²` eigenvalue** at
`|¬A| ≤ |A|`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_nonneg_of_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    0 ≤
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient]
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    norm_nonneg _
  nlinarith [hbiw_nn]

end LatticeSystem.Quantum
