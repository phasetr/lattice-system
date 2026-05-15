import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceReComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# Strict complement predicted `(Ŝ_tot)²` eigenvalue `< m_max·(m_max+1)` at `|A| ≥ 1`

PR #2946 gave strict `< m_max·(m_max+1)` at non-degenerate (`|A| ≥ 1`,
`|¬A| ≥ 1`, `N ≥ 1`, complement orientation `|A| ≤ |¬A|`). This file
generalises by removing the `|¬A| ≥ 1` hypothesis AND orientation:

  `complement_eigenvalue.re < m_max·(m_max+1)`
  at `|A| ≥ 1`, `N ≥ 1`.

Proof: at `|A| ≥ 1`, `biw.re = (|A| − |¬A|)·N/2 > −|Λ|·N/2 = −m_max`
strictly (when `N ≥ 1`), since `|A| - |¬A| ≥ 1 - |Λ| > -|Λ|`.
Combined with the unconditional `biw.re ≤ m_max` (from
`‖biw‖ ≤ m_max` + `biw.im = 0`), the parabola `x·(x-1)` for
`x ∈ (-m_max, m_max]` satisfies
`m_max(m_max+1) − biw.re·(biw.re-1) = (m_max - biw.re + 1)·(m_max + biw.re) > 0`.

Mirror of PR #2947 (generalised strict canonical bound). Sets up
the unified equality characterisation (PR #2956).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Strict complement predicted (Ŝ_tot)² eigenvalue < `m_max·(m_max+1)`** at
`|A| ≥ 1`, `N ≥ 1` (no `|¬A| ≥ 1`, no orientation hypothesis).
Generalises PR #2946 via signed complement form (PR #2955). -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_lt_mMax_quad_of_cardA_pos
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
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
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
        A N]
  -- |biw.re| ≤ m_max (unconditional).
  have hbiw_norm := bipartiteImbalanceWeight_norm_le_mMax (Λ := Λ) A N
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  have habs : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, him]
      simp [Real.sqrt_sq_eq_abs]
    rw [← hnorm_eq]
    exact hbiw_norm
  obtain ⟨hre_ge, hre_le⟩ := abs_le.mp habs
  -- biw.re > -m_max strict (since |A| ≥ 1, N ≥ 1).
  have hre_gt : -((Fintype.card Λ : ℝ) * (N : ℝ) / 2) <
      (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
    rw [bipartiteImbalanceWeight_re_eq]
    have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by
      exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
    have hA_pos : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      exact_mod_cast hA
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hAc_le : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      linarith
    rw [hAc_le]
    nlinarith [hA_pos, hN_pos]
  -- biw.re ∈ (-m_max, m_max] ⟹ biw.re·(biw.re-1) < m_max·(m_max+1).
  nlinarith [hre_gt, hre_le]

end LatticeSystem.Quantum
