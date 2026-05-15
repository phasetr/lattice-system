import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceReComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLeMMax
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# Unified iff: complement predicted `(Ŝ_tot)²` eigenvalue `= m_max·(m_max+1)` ↔ `|A| = 0`

PR #2949 gave the iff at orientation `|A| ≤ |¬A|`. This file gives
the **unified** iff without orientation hypothesis, via PR #2955's
signed complement form:

  `complement_eigenvalue.re = biw.re·(biw.re − 1)`.

Setting this `= m_max·(m_max+1)` and solving:
`(biw.re − (m_max+1))·(biw.re + m_max) = 0`,
so `biw.re ∈ {m_max + 1, −m_max}`. Combined with `|biw.re| ≤ m_max`
(from `‖biw‖ ≤ m_max` + `biw.im = 0`), only `biw.re = −m_max` works.

At `N ≥ 1`, `biw.re = −m_max ↔ (|A| − |¬A|)·N = −|Λ|·N ↔ |A| = 0`.

  `complement_eigenvalue.re = m_max·(m_max + 1) ↔ |A| = 0`
  (at `N ≥ 1`, no orientation hypothesis).

Generalises PR #2949 by removing the `|A| ≤ |¬A|` orientation
hypothesis.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified iff**: complement predicted `(Ŝ_tot)²` eigenvalue
`= m_max·(m_max+1) ↔ |A| = 0` (at `N ≥ 1`, no orientation hypothesis).
Generalises PR #2949 via PR #2955 (signed complement form). -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_mMax_quad_iff_cardA_zero_unified
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
        A N]
  -- |biw.re| ≤ m_max.
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
  -- Goal: biw.re·(biw.re − 1) = m_max·(m_max+1) ↔ |A| = 0.
  constructor
  · intro heq
    -- Factor: (biw.re − (m_max+1))·(biw.re + m_max) = 0.
    have hfact : (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        ((bipartiteImbalanceWeight (Λ := Λ) A N).re - 1) -
          (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
            ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) =
        ((bipartiteImbalanceWeight (Λ := Λ) A N).re -
            ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1)) *
          ((bipartiteImbalanceWeight (Λ := Λ) A N).re +
            (Fintype.card Λ : ℝ) * (N : ℝ) / 2) := by ring
    have hzero : (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        ((bipartiteImbalanceWeight (Λ := Λ) A N).re - 1) -
          (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
            ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) = 0 := by linarith
    rw [hfact] at hzero
    -- biw.re ∈ {m_max + 1, −m_max}.
    rcases mul_eq_zero.mp hzero with h1 | h2
    · -- biw.re = m_max + 1, but biw.re ≤ m_max < m_max + 1: contradiction.
      exfalso; linarith
    · -- biw.re = −m_max.
      have hre_eq : (bipartiteImbalanceWeight (Λ := Λ) A N).re =
          -((Fintype.card Λ : ℝ) * (N : ℝ) / 2) := by linarith
      rw [bipartiteImbalanceWeight_re_eq] at hre_eq
      -- (|A| − |¬A|)·N/2 = −|Λ|·N/2 ⟹ |A| − |¬A| = −|Λ| (since N ≥ 1) ⟹ |A| = 0.
      have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
          (Fintype.card Λ : ℝ) := by
        exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hA_real : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        have h2N : (2 : ℝ) > 0 := by norm_num
        nlinarith [hre_eq, hsum, hN_pos]
      exact_mod_cast hA_real
  · intro h
    -- |A| = 0: biw.re = −m_max ⟹ biw.re·(biw.re − 1) = m_max·(m_max+1).
    rw [bipartiteImbalanceWeight_re_eq, h]
    have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by
      exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
    have hAc_eq : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by
      have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast h
      linarith
    rw [hAc_eq]
    push_cast
    ring

end LatticeSystem.Quantum
