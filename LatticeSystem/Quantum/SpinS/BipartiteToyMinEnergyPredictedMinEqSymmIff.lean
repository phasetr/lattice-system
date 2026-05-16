import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubMinEqAbsSpread
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadZeroIff

/-!
# `min(...) = (predictedSymm A).re ↔ |A| = |¬A|` at `N ≥ 1`

PR #3015: `(predictedSymm A).re − min((predicted_min A).re, (predicted_min ¬A).re) = ||A| − |¬A||·N`.
PR #3013: `spread = 0 ↔ |A| = |¬A|` at `N ≥ 1`.

Combining: at `N ≥ 1`,

  `min((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re
   ↔ |A| = |¬A|`.

At balanced, both predicted min energies coincide with `predictedSymm`,
so `min = max = predictedSymm`. At unbalanced (and `N ≥ 1`), the min
sits strictly below `predictedSymm`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min iff balanced** at `N ≥ 1`: `min((predicted_min A).re,
(predicted_min ¬A).re) = (predictedSymm A).re ↔ |A| = |¬A|`. Companion
of PR #3013 (spread = 0 iff balanced) via PR #3015. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_predictedSymm_re_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hspread :=
    bipartiteToyMinEnergyPredictedSymm_re_sub_min_complement_re_eq (Λ := Λ) A N
  have hspread_zero_iff :=
    bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_zero_iff_balanced
      (Λ := Λ) A N hN
  have hmaxmin :=
    bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq (Λ := Λ) A N
  -- predictedSymm − min = ||A| − |¬A||·N = max − min, so:
  -- min = predictedSymm ↔ predictedSymm − min = 0 ↔ max − min = 0 ↔ balanced.
  constructor
  · intro heq
    have hzero : (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 := by
      linarith
    have hsp : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) = 0 := by
      linarith
    have hmaxmin_zero : max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 := by
      rw [hmaxmin]; exact hsp
    exact hspread_zero_iff.mp hmaxmin_zero
  · intro hbal
    have hmaxmin_zero : max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 :=
      hspread_zero_iff.mpr hbal
    have hsp : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) = 0 := by
      rw [← hmaxmin]; exact hmaxmin_zero
    linarith

end LatticeSystem.Quantum
