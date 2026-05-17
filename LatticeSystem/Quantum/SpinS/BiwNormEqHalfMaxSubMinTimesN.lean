import LatticeSystem.Quantum.SpinS.MaxSubMinTimesNEqTwoBiwNorm

/-!
# `‖biw‖ = (max(|A|, |¬A|) − min(|A|, |¬A|)) · N / 2` unconditionally

Rearrangement of PR #3236 (`max·N − min·N = 2·‖biw‖`):

  `‖biw‖ = (max(|A|, |¬A|) − min(|A|, |¬A|)) · N / 2`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖ = (max − min)·N/2`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_eq_max_sub_min_times_n_div_two
    (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) -
          min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        (N : ℝ) / 2 := by
  have h := max_sub_min_card_times_n_eq_two_biw_norm (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
