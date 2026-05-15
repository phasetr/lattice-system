import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNormComplement

/-!
# Non-negativity of complement predicted `(Ŝ_tot)²` eigenvalue

PR #2931 identified the complement-orientation predicted
`(Ŝ_tot)²` eigenvalue with `‖biw‖·(‖biw‖+1)` at `|A| ≤ |¬A|`.
Since `‖biw‖ ≥ 0`, this is non-negative:

  `((s_B − s_A)·((s_B − s_A) + 1)).re ≥ 0`   at `|A| ≤ |¬A|`.

Mirror of PR #2935. The complement-orientation predicted GS Casimir
eigenvalue is physical (non-negative) exactly under the complement
orientation `|A| ≤ |¬A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Non-negativity of complement predicted `(Ŝ_tot)²` eigenvalue**
at `|A| ≤ |¬A|`. Mirror of PR #2935. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_nonneg_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    0 ≤
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient]
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    norm_nonneg _
  nlinarith [hbiw_nn]

end LatticeSystem.Quantum
