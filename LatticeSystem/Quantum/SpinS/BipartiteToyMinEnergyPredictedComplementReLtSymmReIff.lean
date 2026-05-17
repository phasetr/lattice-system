import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReSubComplementReEqBiwNormAddBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightRePosIff

/-!
# `(pm¬A).re < predictedSymm.re ↔ |¬A| < |A| ∧ 0 < N`

Mirror of PR #3163. The complement predicted-min energy `(pm¬A).re`
sits strictly below the symmetric form `predictedSymm.re` exactly when
the complement is the lighter orientation (i.e. `|¬A| < |A|`) and
`N > 0`.

  `(predicted_min ¬A).re < predictedSymm.re ↔ |¬A| < |A| ∧ 0 < N`.

Strict refinement of existing non-strict
`bipartiteToyMinEnergyPredicted_complement_re_le_predictedSymm_re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(pm¬A).re < predictedSymm.re iff `|¬A| < |A| ∧ 0 < N`**. Mirror of PR #3163. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_lt_predictedSymm_re_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < N := by
  have hgap := bipartiteToyMinEnergyPredictedSymm_re_sub_complement_re_eq_biw_norm_add_biw_re
    (Λ := Λ) A N
  -- Use ‖biw‖ = |biw.re| for the real biw.
  have hi := bipartiteImbalanceWeight_im_zero (Λ := Λ) (A := A) (N := N)
  have hnorm_eq_abs : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
    rw [Complex.norm_def, Complex.normSq_apply, hi]
    have hreplace : (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        (bipartiteImbalanceWeight (Λ := Λ) A N).re =
        (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 := by ring
    simp [hreplace, Real.sqrt_sq_eq_abs]
  constructor
  · intro hlt
    have hgap_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by linarith
    rw [hnorm_eq_abs] at hgap_pos
    -- |x| + x > 0 ↔ x > 0 (real x).
    have hbiw_pos : 0 < (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
      by_contra hnp
      push Not at hnp
      rw [abs_of_nonpos hnp] at hgap_pos
      linarith
    exact (bipartiteImbalanceWeight_re_pos_iff (Λ := Λ) A N).mp hbiw_pos
  · intro ⟨hcard, hN⟩
    have hbiw_pos : 0 < (bipartiteImbalanceWeight (Λ := Λ) A N).re :=
      (bipartiteImbalanceWeight_re_pos_iff (Λ := Λ) A N).mpr ⟨hcard, hN⟩
    have hgap_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
      rw [hnorm_eq_abs, abs_of_pos hbiw_pos]
      linarith
    linarith

end LatticeSystem.Quantum
