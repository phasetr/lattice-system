import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubAvgEqHalfSpread

/-!
# `avg < (predictedSymm A).re ↔ |A| ≠ |¬A|` at `N ≥ 1`

PR #3034: `(predictedSymm A).re − avg = ||A| − |¬A||·N / 2`.

This strict positivity iff: at `N ≥ 1`, the avg sits strictly below
`predictedSymm` exactly at unbalanced (`|A| ≠ |¬A|`):

  `((predicted_min A).re + (predicted_min ¬A).re) / 2 < (predictedSymm A).re
   ↔ |A| ≠ |¬A|`.

Companion strict version of PR #3037 (equality iff balanced).
Together they complete the sign trichotomy of the avg-symm gap.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg < predictedSymm iff unbalanced** at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_lt_predictedSymm_re_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 <
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have h := bipartiteToyMinEnergyPredictedSymm_re_sub_avg_complement_re_eq (Λ := Λ) A N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro hlt hcardeq
    have heq_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcardeq
    have hsub : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by linarith
    have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| = 0 := by
      rw [hsub, abs_zero]
    have hgap_zero : (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 = 0 := by
      rw [h, habs, zero_mul, zero_div]
    linarith
  · intro hne
    have hne_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≠
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hne
    have hsub_ne : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≠ 0 :=
      sub_ne_zero.mpr hne_re
    have habs_pos : 0 < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| := abs_pos.mpr hsub_ne
    have hgap_pos : 0 < (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 := by
      rw [h]; positivity
    linarith

end LatticeSystem.Quantum
