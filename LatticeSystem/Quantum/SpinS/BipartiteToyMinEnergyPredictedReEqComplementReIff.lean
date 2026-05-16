import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# `(pmA).re = (pm¬A).re ↔ balanced` at `N ≥ 1`

PR #3021: `(pmA).re − (pm¬A).re = (|A| − |¬A|)·N`. At `N ≥ 1`:

  `(predicted_min A).re = (predicted_min ¬A).re ↔ |A| = |¬A|`.

The two orientation-specific predicted min energies coincide exactly
at balanced. Real-part version of the existing complex-level iff
`bipartiteToyMinEnergyPredicted_eq_complement_iff_card_eq` (PR #2998).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re = (pm¬A).re iff balanced** at `N ≥ 1`. Real-part
version of PR #2998. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_complement_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hdiff := bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq (Λ := Λ) A N
  have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : ((N : ℝ)) ≠ 0 := ne_of_gt hN_re
  constructor
  · intro heq
    have hdiff_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
      have : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
          (N : ℝ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hN_ne
    have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
    exact_mod_cast heq_re
  · intro hcard
    have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcard
    have hsub_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
    have hprod_zero : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) = 0 := by
      rw [hsub_zero]; ring
    linarith

end LatticeSystem.Quantum
