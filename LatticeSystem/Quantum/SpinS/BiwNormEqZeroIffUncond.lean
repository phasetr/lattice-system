import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# iff: `‖biw‖ = 0 ↔ |A| = |¬A| ∨ N = 0`

Unconditional version (existing `bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq`
requires `N ≥ 1`). From `‖biw‖ = ||A|−|¬A||·N/2`, equal to 0 iff
factor 0 or N = 0.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖ = 0 iff balanced or N = 0`** unconditionally. -/
theorem bipartiteImbalanceWeight_norm_eq_zero_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  rw [bipartiteImbalanceWeight_norm_eq]
  constructor
  · intro heq
    -- |a − b|·(N/2) = 0 → factor 0.
    rcases mul_eq_zero.mp heq with h_abs | h_half
    · left
      have h_diff : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := abs_eq_zero.mp h_abs
      have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
      exact_mod_cast this
    · right
      have hN_re : (N : ℝ) = 0 := by linarith
      exact_mod_cast hN_re
  · intro hor
    rcases hor with hcard | hN
    · have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by exact_mod_cast hcard
      have h_diff : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
      rw [h_diff, abs_zero]; ring
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      rw [hN_re]; ring

end LatticeSystem.Quantum
