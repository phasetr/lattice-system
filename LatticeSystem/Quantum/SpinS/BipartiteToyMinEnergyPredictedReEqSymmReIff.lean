import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReSubReEqBiwNormSubBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightReNonnegIff

/-!
# `(pmA).re = predictedSymm.re ↔ |¬A| ≤ |A| ∨ N = 0`

The canonical predicted-min energy `(pmA).re` equals the symmetric
form `predictedSymm.re` exactly when the canonical orientation is at
least as heavy as the complement (so the predictedSymm-max coincides
with `(pmA).re`) or `N = 0` (degenerate case where both are 0).

  `(predicted_min A).re = predictedSymm.re ↔ |¬A| ≤ |A| ∨ N = 0`.

Equality companion of the strict iff PR #3163. Equivalent to the
existing `BipartiteToyMinEnergyPredictedEqSymmIff.lean` framework
at the real-part level.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re = predictedSymm.re iff `|¬A| ≤ |A| ∨ N = 0`**. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_predictedSymm_re_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card ∨
      N = 0 := by
  have hgap := bipartiteToyMinEnergyPredictedSymm_re_sub_re_eq_biw_norm_sub_biw_re
    (Λ := Λ) A N
  have hi := bipartiteImbalanceWeight_im_zero (Λ := Λ) (A := A) (N := N)
  have hnorm_eq_abs : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
    rw [Complex.norm_def, Complex.normSq_apply, hi]
    have hreplace : (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        (bipartiteImbalanceWeight (Λ := Λ) A N).re =
        (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by ring
    simp [hreplace, Real.sqrt_sq_eq_abs]
  constructor
  · intro heq
    -- predictedSymm.re − (pmA).re = 0 → ‖biw‖ − biw.re = 0 → ‖biw‖ = biw.re → biw.re ≥ 0.
    have hgap_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 := by linarith
    rw [hnorm_eq_abs] at hgap_zero
    -- |x| = x ↔ x ≥ 0.
    have hbiw_nn : 0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
      have habs_eq : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| =
          (bipartiteImbalanceWeight (Λ := Λ) A N).re := by linarith
      exact abs_eq_self.mp habs_eq
    exact (bipartiteImbalanceWeight_re_nonneg_iff (Λ := Λ) A N).mp hbiw_nn
  · intro hor
    have hbiw_nn : 0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re :=
      (bipartiteImbalanceWeight_re_nonneg_iff (Λ := Λ) A N).mpr hor
    have habs_eq : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| =
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := abs_of_nonneg hbiw_nn
    have hgap_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 := by
      rw [hnorm_eq_abs, habs_eq]; ring
    linarith

end LatticeSystem.Quantum
