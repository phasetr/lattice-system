import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLeSymmRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedLtSymmIff

/-!
# Iff: `(predicted_min A).re = (predictedSymm A).re ↔ |¬A| ≤ |A|` at `N ≥ 1`

PR #2999: `(predicted_min A).re ≤ (predictedSymm A).re` unconditionally.
PR #3007: `(predicted_min A).re < (predictedSymm A).re ↔ |A| < |¬A|` at `N ≥ 1`.

Combining (`= ↔ ≤ ∧ NOT <`), at `N ≥ 1`:

  `(predicted_min A).re = (predictedSymm A).re ↔ ¬(|A| < |¬A|) ↔ |¬A| ≤ |A|`.

The trichotomy iff: canonical predicted min energy matches the symmetric
form exactly at proper orientation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff equality**: `(predicted_min A).re = (predictedSymm A).re ↔
|¬A| ≤ |A|` at `N ≥ 1`. Trichotomy companion of PR #3007. -/
theorem bipartiteToyMinEnergyPredicted_re_eq_predictedSymm_re_iff_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
  have hle := bipartiteToyMinEnergyPredicted_re_le_predictedSymm_re (Λ := Λ) A N
  have hlt_iff := bipartiteToyMinEnergyPredicted_re_lt_predictedSymm_re_iff_cardA_lt_cardNotA
    (Λ := Λ) A N hN
  constructor
  · intro heq
    -- = ⟹ ¬ <. Combined with hlt_iff: ¬ (|A| < |¬A|), i.e., |¬A| ≤ |A|.
    by_contra hnotle
    push Not at hnotle
    -- hnotle : |A| < |¬A|.
    have hlt := hlt_iff.mpr hnotle
    linarith
  · intro hor
    -- |¬A| ≤ |A| ⟹ ¬ (|A| < |¬A|) ⟹ ¬ <, combined with hle gives =.
    have hnotlt : ¬ (Finset.univ.filter (fun x : Λ => A x = true)).card <
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
      intro hlt; exact absurd hor (not_le_of_gt hlt)
    have hnotlt_re : ¬ (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
      intro hlt_re; exact hnotlt (hlt_iff.mp hlt_re)
    linarith

end LatticeSystem.Quantum
