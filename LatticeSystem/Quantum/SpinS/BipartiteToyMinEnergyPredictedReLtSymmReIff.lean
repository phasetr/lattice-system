import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReSubReEqBiwNormSubBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightReNegIff
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqRe

/-!
# `(pmA).re < predictedSymm.re ↔ |A| < |¬A| ∧ 0 < N`

The canonical predicted-min energy `(pmA).re` sits strictly below the
symmetric form `predictedSymm.re` exactly when the canonical orientation
is *not* the lighter one (i.e. `|A| < |¬A|`) and `N > 0`. At balanced
or `|A| ≥ |¬A|` or `N = 0`, equality holds (PR #3161 gives gap =
`‖biw‖ − biw.re`, which is 0 iff `biw.re ≥ 0` iff complement of strict).

  `(predicted_min A).re < predictedSymm.re ↔ |A| < |¬A| ∧ 0 < N`.

Strict refinement of existing non-strict PR `bipartiteToyMinEnergyPredicted_re_le_predictedSymm_re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re < predictedSymm.re iff `|A| < |¬A| ∧ 0 < N`**. -/
theorem bipartiteToyMinEnergyPredicted_re_lt_predictedSymm_re_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  have hgap := bipartiteToyMinEnergyPredictedSymm_re_sub_re_eq_biw_norm_sub_biw_re
    (Λ := Λ) A N
  constructor
  · intro hlt
    -- predictedSymm − pmA > 0 → ‖biw‖ − biw.re > 0 → ‖biw‖ > biw.re → biw.re < 0.
    have hgap_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by linarith
    -- ‖biw‖ > biw.re iff biw.re < 0 (since ‖biw‖ = |biw.re| and biw is real).
    have hnorm_ge : (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
      rw [Complex.norm_def]
      have hi := bipartiteImbalanceWeight_im_zero (Λ := Λ) (A := A) (N := N)
      have : Complex.normSq (bipartiteImbalanceWeight (Λ := Λ) A N) =
          ((bipartiteImbalanceWeight (Λ := Λ) A N).re)^2 := by
        rw [Complex.normSq_apply, hi]; ring
      rw [this, Real.sqrt_sq_eq_abs]
      exact le_abs_self _
    -- Strict ‖biw‖ > biw.re holds iff biw.re ≠ ‖biw‖, which holds iff biw.re < 0.
    -- biw is real so ‖biw‖ = |biw.re|. Then |biw.re| > biw.re iff biw.re < 0.
    have hi := bipartiteImbalanceWeight_im_zero (Λ := Λ) (A := A) (N := N)
    have hnorm_eq_abs : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
      rw [Complex.norm_def, Complex.normSq_apply, hi]
      have hreplace : (bipartiteImbalanceWeight (Λ := Λ) A N).re *
          (bipartiteImbalanceWeight (Λ := Λ) A N).re =
          (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by ring
      simp [hreplace, Real.sqrt_sq_eq_abs]
    rw [hnorm_eq_abs] at hgap_pos
    have hbiw_neg : (bipartiteImbalanceWeight (Λ := Λ) A N).re < 0 := by
      by_contra hnn
      push Not at hnn
      rw [abs_of_nonneg hnn] at hgap_pos
      linarith
    exact (bipartiteImbalanceWeight_re_neg_iff (Λ := Λ) A N).mp hbiw_neg
  · intro ⟨hcard, hN⟩
    have hbiw_neg : (bipartiteImbalanceWeight (Λ := Λ) A N).re < 0 :=
      (bipartiteImbalanceWeight_re_neg_iff (Λ := Λ) A N).mpr ⟨hcard, hN⟩
    have hi := bipartiteImbalanceWeight_im_zero (Λ := Λ) (A := A) (N := N)
    have hnorm_eq_abs : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
        |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
      rw [Complex.norm_def, Complex.normSq_apply, hi]
      have hreplace : (bipartiteImbalanceWeight (Λ := Λ) A N).re *
          (bipartiteImbalanceWeight (Λ := Λ) A N).re =
          (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by ring
      simp [hreplace, Real.sqrt_sq_eq_abs]
    have hnorm_pos : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re > 0 := by
      rw [hnorm_eq_abs, abs_of_neg hbiw_neg]
      linarith
    linarith

end LatticeSystem.Quantum
