import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNormComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax

/-!
# Upper bound: complement predicted `(Ŝ_tot)²` eigenvalue ≤ `m_max·(m_max + 1)`

PR #2931 gave the complement-orientation eigenvalue identification
at `|A| ≤ |¬A|`:
`((s_B − s_A)·((s_B − s_A) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

PR #2874 gives `‖biw‖ ≤ |Λ|·N/2 = m_max`. Since `x ↦ x·(x+1)` is
monotonic increasing on `[0, ∞)`, the complement-orientation predicted
eigenvalue is bounded above by `m_max·(m_max + 1)`:

  `complement predicted (Ŝ_tot)² eigenvalue ≤ m_max·(m_max + 1)`
  at `|A| ≤ |¬A|`.

Mirror of PR #2942. The complement-orientation predicted GS Casimir
eigenvalue also cannot exceed the fully-polarised ferromagnetic value.
Equality is attained at the saturated complement (PR #2941).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Upper bound on complement predicted (Ŝ_tot)² eigenvalue**:
≤ `m_max·(m_max + 1)` at `|A| ≤ |¬A|`. Mirror of PR #2942 via PR #2931
+ PR #2874. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_le_mMax_quad_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient]
  -- ‖biw‖ ≤ |Λ|·N/2.
  have hbiw := bipartiteImbalanceWeight_norm_le_mMax (Λ := Λ) A N
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  -- Use monotonicity of x·(x+1) on [0, ∞).
  nlinarith [hbiw, hbiw_nn]

end LatticeSystem.Quantum
