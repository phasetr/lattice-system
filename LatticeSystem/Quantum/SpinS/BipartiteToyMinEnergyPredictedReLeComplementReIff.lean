import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReLtComplementReIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReEqComplementReIff

/-!
# `(pmA).re ≤ (pm¬A).re ↔ |A| ≤ |¬A|` at `N ≥ 1`

Non-strict version combining PR #3066 (equality iff balanced) +
PR #3067 (strict iff strict). At `N ≥ 1`:

  `(predicted_min A).re ≤ (predicted_min ¬A).re ↔ |A| ≤ |¬A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re ≤ (pm¬A).re iff `|A| ≤ |¬A|`** at `N ≥ 1`. Combines
PR #3066 + PR #3067. -/
theorem bipartiteToyMinEnergyPredicted_re_le_complement_re_iff_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have heq_iff := bipartiteToyMinEnergyPredicted_re_eq_complement_re_iff_balanced
    (Λ := Λ) A N hN
  have hlt_iff := bipartiteToyMinEnergyPredicted_re_lt_complement_re_iff_cardA_lt_cardNotA
    (Λ := Λ) A N hN
  constructor
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (hlt_iff.mp hlt)
    · exact le_of_eq (heq_iff.mp heq)
  · intro hcard_le
    rcases lt_or_eq_of_le hcard_le with hlt | heq
    · exact le_of_lt (hlt_iff.mpr hlt)
    · exact le_of_eq (heq_iff.mpr heq)

end LatticeSystem.Quantum
