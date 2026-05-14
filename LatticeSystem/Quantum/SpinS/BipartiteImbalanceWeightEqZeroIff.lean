import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `bipartiteImbalanceWeight A N = 0` characterisation

PR #2773 proved
`|A| = |¬A| → bipartiteImbalanceWeight A N = 0`.

This file adds the converse (for `N ≥ 1`):
`bipartiteImbalanceWeight A N = 0 → |A| = |¬A|`, hence the iff
`bipartiteImbalanceWeight A N = 0 ↔ |A| = |¬A|` at `N ≥ 1`.

(At `N = 0` the weight is always `0` regardless of cardinalities,
hence the hypothesis is needed.)

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) {N : ℕ}

/-- **Reverse direction**: `bipartiteImbalanceWeight A N = 0` implies
`|A| = |¬A|` (assuming `N ≥ 1`). -/
theorem card_eq_of_bipartiteImbalanceWeight_eq_zero
    (hN : 1 ≤ N)
    (h : bipartiteImbalanceWeight (Λ := Λ) A N = 0) :
    (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hreal := bipartiteImbalanceWeight_re_eq A N
  have h_re_zero : (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 := by
    rw [h]; simp
  rw [hreal] at h_re_zero
  -- h_re_zero : (|A| - |¬A|) * (N/2) = 0.
  -- Since N ≥ 1, N/2 > 0, hence |A| - |¬A| = 0.
  have hN_pos : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hdiff : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
    -- h_re_zero : (|A| - |¬A|) * (N/2) = 0, divide both sides by N/2 > 0.
    have hN_ne_zero : ((N : ℝ) / 2) ≠ 0 := ne_of_gt hN_pos
    exact (mul_eq_zero.mp h_re_zero).resolve_right hN_ne_zero
  have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    linarith
  exact_mod_cast this

/-- **`bipartiteImbalanceWeight = 0 ↔ |A| = |¬A|`** (at `N ≥ 1`). -/
theorem bipartiteImbalanceWeight_eq_zero_iff_card_eq
    (hN : 1 ≤ N) :
    bipartiteImbalanceWeight (Λ := Λ) A N = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
  ⟨card_eq_of_bipartiteImbalanceWeight_eq_zero A hN,
   bipartiteImbalanceWeight_eq_zero_of_card_eq A N⟩

end LatticeSystem.Quantum
