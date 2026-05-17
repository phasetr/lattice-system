import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `min(|A|, |¬A|) · N = (|A|+|¬A|)·N/2 − ‖biw‖` unconditionally

Mirror of PR #3232. From `2·min = (a + b) − |a − b|`:

  `min(|A|, |¬A|) · N = (|A|+|¬A|)·N/2 − ‖biw‖`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`min(|A|, |¬A|)·N = (|A|+|¬A|)·N/2 − ‖biw‖`** unconditionally. Mirror of PR #3232. -/
theorem min_card_times_n_eq_half_card_sub_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) / 2 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteImbalanceWeight_norm_eq]
  have h_sum := max_add_min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  have h_diff := max_sub_min_eq_abs ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  rw [abs_sub_comm] at h_diff
  nlinarith [h_sum, h_diff, sq_nonneg ((N : ℝ))]

end LatticeSystem.Quantum
