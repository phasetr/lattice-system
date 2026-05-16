import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgSubMinEqHalfSpread

/-!
# `min((pmA).re, (pm¬A).re) = avg ↔ |A| = |¬A|` at `N ≥ 1`

PR #3039: `avg − min = ||A| − |¬A||·N / 2`.

This vanishes at balanced (modulo the `N = 0` edge case). At `N ≥ 1`:

  `min((predicted_min A).re, (predicted_min ¬A).re)
   = ((predicted_min A).re + (predicted_min ¬A).re) / 2
   ↔ |A| = |¬A|`.

At balanced both orientation-specific predicted min energies coincide,
so min = max = avg. At unbalanced (and `N ≥ 1`), the min sits
strictly below the average by half the orientation-spread.

Mirror of PR #3037 (avg = predictedSymm iff balanced) for the lower
end of the orientation sandwich.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min = avg iff balanced** at `N ≥ 1`. Mirror of PR #3037 for
the lower end of the orientation sandwich. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have h := bipartiteToyMinEnergyPredicted_avg_complement_re_sub_min_eq (Λ := Λ) A N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNpos
  constructor
  · intro heq
    have hgap_zero : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 := by
      linarith
    have habs_mul : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) = 0 := by linarith
    have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| = 0 := by
      rcases mul_eq_zero.mp habs_mul with h | h
      · exact h
      · exact absurd h hNne
    have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := abs_eq_zero.mp habs
    have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by linarith
    exact_mod_cast heq_re
  · intro hcard
    have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcard
    have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
    have habs_mul : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) = 0 := by rw [hsub, abs_zero, zero_mul]
    linarith

end LatticeSystem.Quantum
