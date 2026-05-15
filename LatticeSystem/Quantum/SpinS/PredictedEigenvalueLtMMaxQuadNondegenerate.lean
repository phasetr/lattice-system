import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLtMMaxNondegenerate
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Strict upper bound: predicted `(Ŝ_tot)²` eigenvalue `< m_max·(m_max + 1)` at non-degenerate

PR #2944 gave the unified upper bound `eigenvalue.re ≤ m_max·(m_max+1)`.
At the **non-degenerate** configuration (`|A| ≥ 1`, `|¬A| ≥ 1`,
`N ≥ 1`) the inequality is **strict**:

  `predicted (Ŝ_tot)² eigenvalue < m_max·(m_max + 1)`.

Proof: PR #2877 (`bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate`)
gives `‖biw‖ < m_max`. Since `biw.im = 0`, `|biw.re| = ‖biw‖ < m_max`,
so `−m_max < biw.re < m_max`. The parabola `x ↦ x·(x+1)` on
`(−m_max, m_max)` is strictly less than `m_max·(m_max+1)`, established
via `nlinarith` from `(m_max − biw.re) > 0` and
`(m_max + biw.re + 1) ≥ 1 > 0` (both factors positive, product positive,
difference `m_max(m_max+1) − biw.re(biw.re+1) > 0`).

Together with the unified PR #2944 upper bound, this completes the
"saturated iff equality" characterisation: at non-degenerate, the
predicted GS Casimir eigenvalue is strictly less than the fully-polarised
ferromagnetic value.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Strict upper bound on predicted (Ŝ_tot)² eigenvalue at non-degenerate**:
`< m_max·(m_max + 1)` when `|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`. Strengthens
PR #2944 via PR #2877 (strict imbalance-norm bound). -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_lt_mMax_quad_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N]
  -- ‖biw‖ < m_max and biw.im = 0 ⟹ |biw.re| < m_max.
  have hbiw_norm_lt :=
    bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate A N hA hAc hN
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  have habs_lt : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, him]
      simp [Real.sqrt_sq_eq_abs]
    rw [← hnorm_eq]
    exact hbiw_norm_lt
  obtain ⟨hre_gt, hre_lt⟩ := abs_lt.mp habs_lt
  -- biw.re ∈ (−m_max, m_max) ⟹ biw.re·(biw.re+1) < m_max·(m_max+1).
  nlinarith [hre_gt, hre_lt]

end LatticeSystem.Quantum
