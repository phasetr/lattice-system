import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxMinDiff
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqZero

/-!
# Iff: `max − min > 0 ↔ unbalanced` at `N ≥ 1`

PR #2968: `max(canonical, complement) − min(canonical, complement) = 2·‖biw‖`.

PR #2855: `‖biw‖ = 0 ↔ balanced` at `N ≥ 1`, hence
`‖biw‖ > 0 ↔ unbalanced`.

Hence

  `max(canonical, complement) − min(canonical, complement) > 0 ↔
     |A| ≠ |¬A|`   at `N ≥ 1`.

The canonical-complement eigenvalue gap (proportional to `‖biw‖`)
vanishes iff the configuration is balanced; otherwise strictly
positive. Companion of PR #2971 (`max > 0 ↔ unbalanced`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff**: `max − min > 0 ↔ unbalanced` at `N ≥ 1`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_sub_min_pos_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) :
    0 < max
            ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                      ((N : ℂ) / 2) -
                    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                      ((N : ℂ) / 2)) + 1)).re
            ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                      ((N : ℂ) / 2) -
                    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                      ((N : ℂ) / 2)) + 1)).re -
          min
              ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                      ((N : ℂ) / 2) -
                    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                      ((N : ℂ) / 2)) *
                  ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                        ((N : ℂ) / 2) -
                      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                        ((N : ℂ) / 2)) + 1)).re
              ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                      ((N : ℂ) / 2) -
                    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                      ((N : ℂ) / 2)) *
                  ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                        ((N : ℂ) / 2) -
                      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                        ((N : ℂ) / 2)) + 1)).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_sub_min_eq_two_norm
        A N]
  -- 2·‖biw‖ > 0 ↔ ‖biw‖ > 0 ↔ unbalanced (at N ≥ 1).
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  constructor
  · intro hpos hbal
    have hbiw_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 :=
      (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mpr hbal
    rw [hbiw_zero] at hpos
    linarith
  · intro hne
    have hbiw_ne : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≠ 0 := by
      intro hzero
      have : (Finset.univ.filter (fun x : Λ => A x = true)).card =
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
        (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mp hzero
      exact hne this
    have hbiw_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
      lt_of_le_of_ne hbiw_nn (Ne.symm hbiw_ne)
    linarith

end LatticeSystem.Quantum
