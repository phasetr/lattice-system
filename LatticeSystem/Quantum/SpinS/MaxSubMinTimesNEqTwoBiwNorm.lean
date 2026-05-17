import LatticeSystem.Quantum.SpinS.MaxTimesNEqHalfCardAddBiwNorm
import LatticeSystem.Quantum.SpinS.MinTimesNEqHalfCardSubBiwNorm

/-!
# `max·N − min·N = 2 · ‖biw‖` unconditionally

Difference of PRs #3232 − #3234. The cardinality sums cancel:

  `max(|A|, |¬A|)·N − min(|A|, |¬A|)·N = 2 · ‖biw‖`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max·N − min·N = 2·‖biw‖`** unconditionally. -/
theorem max_sub_min_card_times_n_eq_two_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) -
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) =
      2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have h1 := max_card_times_n_eq_half_card_add_biw_norm (Λ := Λ) A N
  have h2 := min_card_times_n_eq_half_card_sub_biw_norm (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
