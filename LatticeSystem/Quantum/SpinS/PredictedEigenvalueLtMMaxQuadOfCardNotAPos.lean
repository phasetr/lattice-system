import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Strict predicted `(Ŝ_tot)²` eigenvalue `< m_max·(m_max+1)` at `|¬A| ≥ 1`

PR #2945 gave strict `< m_max·(m_max+1)` at non-degenerate (`|A| ≥ 1`,
`|¬A| ≥ 1`, `N ≥ 1`). This file generalises by removing the
`|A| ≥ 1` hypothesis:

  `predicted (Ŝ_tot)² eigenvalue < m_max·(m_max + 1)`
  at `|¬A| ≥ 1`, `N ≥ 1`.

Proof: at `|¬A| ≥ 1`, `biw.re = (|A| - |¬A|)·N/2 < |Λ|·N/2 = m_max`
strictly (when `N ≥ 1`), since `|A| - |¬A| ≤ |Λ| - 1 < |Λ|`. Combined
with the unconditional `−m_max ≤ biw.re` (from `‖biw‖ ≤ m_max`),
the parabola `x·(x+1)` satisfies
`m_max(m_max+1) − biw.re(biw.re+1) = (m_max − biw.re)(m_max + biw.re + 1) > 0`.

Setting up the equality characterisation: `eigenvalue.re = m_max(m_max+1)`
forces `|¬A| = 0` (the saturated edge in the `(s_A − s_B)` orientation).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Strict predicted (Ŝ_tot)² eigenvalue < `m_max·(m_max+1)`** at
`|¬A| ≥ 1`, `N ≥ 1`. Generalises PR #2945 by removing the `|A| ≥ 1`
hypothesis. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_lt_mMax_quad_of_cardNotA_pos
    (A : Λ → Bool) (N : ℕ)
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
  -- biw.re = (|A| - |¬A|)·N/2; need biw.re < m_max strictly and biw.re ≥ −m_max.
  have hbiw_norm := bipartiteImbalanceWeight_norm_le_mMax (Λ := Λ) A N
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  -- |biw.re| ≤ m_max (unconditional from ‖biw‖ ≤ m_max + im = 0).
  have habs : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, him]
      simp [Real.sqrt_sq_eq_abs]
    rw [← hnorm_eq]
    exact hbiw_norm
  -- biw.re < m_max strict (since |¬A| ≥ 1, N ≥ 1).
  have hre_lt : (bipartiteImbalanceWeight (Λ := Λ) A N).re <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    rw [bipartiteImbalanceWeight_re_eq]
    have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by
      exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
    have hAc_pos : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hAc
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hA_le : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      linarith
    rw [hA_le]
    nlinarith [hAc_pos, hN_pos]
  obtain ⟨hre_ge, _⟩ := abs_le.mp habs
  -- biw.re ∈ [−m_max, m_max) ⟹ biw.re·(biw.re+1) < m_max·(m_max+1).
  nlinarith [hre_ge, hre_lt]

end LatticeSystem.Quantum
