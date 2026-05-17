import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReSubComplementReEqBiwNormAddBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightReNonposIff

/-!
# `(pm¬A).re = predictedSymm.re ↔ |A| ≤ |¬A| ∨ N = 0`

Mirror of PR #3165. The complement predicted-min energy equals the
symmetric form exactly when the complement is at least as heavy as
the canonical orientation (so the complement attains the max) or
`N = 0`.

  `(predicted_min ¬A).re = predictedSymm.re ↔ |A| ≤ |¬A| ∨ N = 0`.

Equality companion of strict iff PR #3164.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(pm¬A).re = predictedSymm.re iff `|A| ≤ |¬A| ∨ N = 0`**. Mirror of PR #3165. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_eq_predictedSymm_re_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  have hgap := bipartiteToyMinEnergyPredictedSymm_re_sub_complement_re_eq_biw_norm_add_biw_re
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
    -- gap = ‖biw‖ + biw.re = 0 → |biw.re| = -biw.re → biw.re ≤ 0.
    have hgap_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 := by linarith
    rw [hnorm_eq_abs] at hgap_zero
    have hbiw_np : (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 := by
      have habs_eq : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| =
          -(bipartiteImbalanceWeight (Λ := Λ) A N).re := by linarith
      exact abs_eq_neg_self.mp habs_eq
    exact (bipartiteImbalanceWeight_re_nonpos_iff (Λ := Λ) A N).mp hbiw_np
  · intro hor
    have hbiw_np : (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 :=
      (bipartiteImbalanceWeight_re_nonpos_iff (Λ := Λ) A N).mpr hor
    have habs_eq : |(bipartiteImbalanceWeight (Λ := Λ) A N).re| =
        -(bipartiteImbalanceWeight (Λ := Λ) A N).re := abs_of_nonpos hbiw_np
    have hgap_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 := by
      rw [hnorm_eq_abs, habs_eq]; ring
    linarith

end LatticeSystem.Quantum
