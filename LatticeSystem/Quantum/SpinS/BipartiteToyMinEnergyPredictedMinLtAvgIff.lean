import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgSubMinEqHalfSpread

/-!
# `min((pmA).re, (pm¬A).re) < avg ↔ |A| ≠ |¬A|` at `N ≥ 1`

Mirror of PR #3038 for the lower end of the sandwich. Companion
strict version of PR #3040 (equality iff balanced).

PR #3039: `avg − min = ||A| − |¬A||·N / 2`. At `N ≥ 1`:

  `min((predicted_min A).re, (predicted_min ¬A).re) < avg
   ↔ |A| ≠ |¬A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min < avg iff unbalanced** at `N ≥ 1`. Mirror of PR #3038. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_lt_avg_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have h := bipartiteToyMinEnergyPredicted_avg_complement_re_sub_min_eq (Λ := Λ) A N
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
    have hgap_zero : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 := by
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
    have hgap_pos : 0 < ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
      rw [h]; positivity
    linarith

end LatticeSystem.Quantum
