import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNormComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLtMMaxNondegenerate

/-!
# Strict complement predicted `(Ŝ_tot)²` eigenvalue `< m_max·(m_max+1)` at non-degenerate

PR #2943 gave the weak complement upper bound at `|A| ≤ |¬A|`:
`((s_B − s_A)·((s_B − s_A) + 1)).re ≤ m_max·(m_max+1)`.

At the **non-degenerate** configuration (`|A| ≥ 1`, `|¬A| ≥ 1`,
`N ≥ 1`) the inequality is **strict**:

  `complement predicted (Ŝ_tot)² eigenvalue < m_max·(m_max + 1)`
  at `|A| ≤ |¬A|`.

Mirror of PR #2945. Proof: PR #2877 gives `‖biw‖ < m_max` at
non-degenerate; combine with PR #2931 (complement = `‖biw‖·(‖biw‖+1)`)
and monotonicity of `x·(x+1)` on `[0, m_max)` via `nlinarith`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Strict upper bound on complement predicted (Ŝ_tot)² eigenvalue
at non-degenerate**: `< m_max·(m_max + 1)` at `|A| ≤ |¬A|`, `|A| ≥ 1`,
`|¬A| ≥ 1`, `N ≥ 1`. Mirror of PR #2945. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_lt_mMax_quad_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
        A N horient]
  -- ‖biw‖ < m_max at non-degenerate.
  have hbiw_lt :=
    bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate A N hA hAc hN
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  -- Strict monotonicity of x·(x+1) at x = ‖biw‖ < m_max.
  nlinarith [hbiw_lt, hbiw_nn]

end LatticeSystem.Quantum
