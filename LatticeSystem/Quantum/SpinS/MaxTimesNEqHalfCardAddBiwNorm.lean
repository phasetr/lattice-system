import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `max(|A|, |¬A|) · N = |Λ|·N/2 + ‖biw‖` unconditionally

Closed-form for `max·N` in terms of `|Λ|` and `‖biw‖`:

  `max(|A|, |¬A|) · N = |Λ|·N/2 + ‖biw‖`

unconditionally, where `‖biw‖ = ||A|−|¬A||·N/2`. From the identity
`max(a, b) = (a + b)/2 + |a−b|/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(|A|, |¬A|)·N = |Λ|·N/2 + ‖biw‖`** unconditionally. -/
theorem max_card_times_n_eq_half_card_add_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) / 2 +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteImbalanceWeight_norm_eq]
  have h_sum := max_add_min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  have h_diff := max_sub_min_eq_abs ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  -- h_diff has |¬A - A|; want |A - ¬A|. Use abs_sub_comm.
  rw [abs_sub_comm] at h_diff
  nlinarith [h_sum, h_diff, sq_nonneg ((N : ℝ))]

end LatticeSystem.Quantum
