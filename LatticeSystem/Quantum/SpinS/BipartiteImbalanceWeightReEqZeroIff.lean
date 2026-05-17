import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `biw.re = 0 ↔ |A| = |¬A| ∨ N = 0`

`biw.re = (|A| − |¬A|) · N / 2`. Vanishes iff either the cardinality
difference vanishes (balanced) or `N = 0`.

Companion to PR #3151 (strict positivity) and PR #3152 (strict
negativity). Together these classify the sign of `biw.re`
completely.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`biw.re = 0 iff `|A| = |¬A| ∨ N = 0`**. -/
theorem bipartiteImbalanceWeight_re_eq_zero_iff
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  rw [bipartiteImbalanceWeight_re_eq]
  constructor
  · intro heq
    -- (|A| − |¬A|) * (N / 2) = 0 → either factor zero.
    have hsplit : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) = 0 ∨
        ((N : ℝ) / 2) = 0 := by
      rcases mul_eq_zero.mp heq with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hsplit with hdiff | hN
    · left
      have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
      exact_mod_cast this
    · right
      have hN_zero : (N : ℝ) = 0 := by linarith
      exact_mod_cast hN_zero
  · intro hor
    rcases hor with hcard | hN
    · have hcard_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hcard
      have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
      rw [this]; ring
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      have : (N : ℝ) / 2 = 0 := by rw [hN_re]; ring
      rw [this]; ring

end LatticeSystem.Quantum
