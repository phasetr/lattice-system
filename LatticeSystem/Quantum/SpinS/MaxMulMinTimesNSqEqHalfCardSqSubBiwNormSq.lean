import LatticeSystem.Quantum.SpinS.MaxTimesNEqHalfCardAddBiwNorm
import LatticeSystem.Quantum.SpinS.MinTimesNEqHalfCardSubBiwNorm

/-!
# `(max·N)(min·N) = (|Λ|·N/2)² − ‖biw‖²` unconditionally

Product of PRs #3232 + #3234 via difference-of-squares:

  `(max(|A|, |¬A|)·N) · (min(|A|, |¬A|)·N) = (|Λ|·N/2)² − ‖biw‖²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`(max·N)·(min·N) = (|Λ|·N/2)² − ‖biw‖²`** unconditionally. -/
theorem max_mul_min_card_times_n_sq_eq_half_card_sq_sub_biw_norm_sq
    (A : Λ → Bool) (N : ℕ) :
    (max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ)) *
      (min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ)) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) / 2 *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) / 2) -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 := by
  have h1 := max_card_times_n_eq_half_card_add_biw_norm (Λ := Λ) A N
  have h2 := min_card_times_n_eq_half_card_sub_biw_norm (Λ := Λ) A N
  rw [h1, h2]
  ring

end LatticeSystem.Quantum
