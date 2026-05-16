import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubMinEqAbsSpread
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadPosIff

/-!
# `min(...) < (predictedSymm A).re ↔ |A| ≠ |¬A|` at `N ≥ 1`

PR #3015: `(predictedSymm A).re − min((pmA).re, (pm¬A).re) = ||A| − |¬A||·N`.
PR #3014: `0 < spread ↔ |A| ≠ |¬A|` at `N ≥ 1`.

Combining: at `N ≥ 1`,

  `min((predicted_min A).re, (predicted_min ¬A).re) < (predictedSymm A).re
   ↔ |A| ≠ |¬A|`.

Companion strict version of PR #3016 (equality iff balanced).
Together they characterise the orientation-spread of the predicted
min energy relative to the symmetric Tasaki §2.5 Theorem 2.3
prediction.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min strict iff unbalanced** at `N ≥ 1`: the min of orientation-
specific predicted min energies sits strictly below `predictedSymm`
exactly at unbalanced. Companion strict version of PR #3016. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_lt_predictedSymm_re_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hspread :=
    bipartiteToyMinEnergyPredictedSymm_re_sub_min_complement_re_eq (Λ := Λ) A N
  have hpos_iff :=
    bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_pos_iff_unbalanced
      (Λ := Λ) A N hN
  have hmaxmin :=
    bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq (Λ := Λ) A N
  -- min < predictedSymm ↔ 0 < predictedSymm − min ↔ 0 < ||A| − |¬A||·N ↔ 0 < max − min ↔ unbalanced.
  constructor
  · intro hlt
    have hsub_pos : 0 < (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
      linarith
    have habs_pos : 0 < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) := by
      linarith
    have hmaxmin_pos : 0 < max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re := by
      rw [hmaxmin]; exact habs_pos
    exact hpos_iff.mp hmaxmin_pos
  · intro hne
    have hmaxmin_pos : 0 < max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
      hpos_iff.mpr hne
    have habs_pos : 0 < |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) := by
      rw [← hmaxmin]; exact hmaxmin_pos
    linarith

end LatticeSystem.Quantum
