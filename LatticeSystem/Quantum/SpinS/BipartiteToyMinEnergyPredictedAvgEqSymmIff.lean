import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubAvgEqHalfSpread

/-!
# `avg = (predictedSymm A).re ↔ |A| = |¬A|` at `N ≥ 1`

PR #3034: `(predictedSymm A).re − avg = ||A| − |¬A||·N / 2`.

This vanishes exactly when `||A| − |¬A|| = 0` (i.e. balanced), modulo
the `N = 0` edge case. At `N ≥ 1`:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2 = (predictedSymm A).re
   ↔ |A| = |¬A|`.

At balanced both orientation-specific predicted min energies coincide
with `predictedSymm`, so their average also equals `predictedSymm`.
At unbalanced (and `N ≥ 1`), the average sits strictly below
`predictedSymm` by half the orientation-spread.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg = predictedSymm iff balanced** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_eq_predictedSymm_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have h := bipartiteToyMinEnergyPredictedSymm_re_sub_avg_complement_re_eq (Λ := Λ) A N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNpos
  constructor
  · intro heq
    have hzero : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) / 2 = 0 := by
      linarith
    have habs_mul : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) = 0 := by
      linarith
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
    have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| = 0 := by
      rw [hsub, abs_zero]
    have habs_mul : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) = 0 := by
      rw [habs, zero_mul]
    linarith

end LatticeSystem.Quantum
