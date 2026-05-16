import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementReLeSymmRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementLtSymmIff

/-!
# Iff: `(predicted_min ¬A).re = (predictedSymm A).re ↔ |A| ≤ |¬A|` at `N ≥ 1`

Mirror of PR #3009.

PR #3000: `(predicted_min ¬A).re ≤ (predictedSymm A).re` unconditionally.
PR #3008: `(predicted_min ¬A).re < (predictedSymm A).re ↔ |¬A| < |A|` at `N ≥ 1`.

Combining (`= ↔ ≤ ∧ NOT <`), at `N ≥ 1`:

  `(predicted_min ¬A).re = (predictedSymm A).re ↔ ¬(|¬A| < |A|) ↔ |A| ≤ |¬A|`.

The complement-orientation predicted min energy matches the symmetric
form exactly at complement orientation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff equality (complement)**: `(predicted_min ¬A).re = (predictedSymm A).re ↔
|A| ≤ |¬A|` at `N ≥ 1`. Mirror of PR #3009. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_eq_predictedSymm_re_iff_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hle := bipartiteToyMinEnergyPredicted_complement_re_le_predictedSymm_re (Λ := Λ) A N
  have hlt_iff := bipartiteToyMinEnergyPredicted_complement_re_lt_predictedSymm_re_iff_cardNotA_lt_cardA
    (Λ := Λ) A N hN
  constructor
  · intro heq
    by_contra hnotle
    push Not at hnotle
    -- hnotle : |¬A| < |A|.
    have hlt := hlt_iff.mpr hnotle
    linarith
  · intro hor
    have hnotlt : ¬ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
      intro hlt; exact absurd hor (not_le_of_gt hlt)
    have hnotlt_re : ¬ (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
      intro hlt_re; exact hnotlt (hlt_iff.mp hlt_re)
    linarith

end LatticeSystem.Quantum
