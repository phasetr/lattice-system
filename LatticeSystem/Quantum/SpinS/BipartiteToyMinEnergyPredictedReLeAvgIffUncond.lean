import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubAvgEqBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightReNonposIff

/-!
# `(pmA).re ≤ avg ↔ |A| ≤ |¬A| ∨ N = 0` unconditionally

Unconditional companion of PR #3135 (`(pmA).re ≤ avg ↔ |A| ≤ |¬A|` at
`N ≥ 1`). Combines PR #3157 (`(pmA).re − avg = biw.re`) with PR #3156
(`biw.re ≤ 0 ↔ |A| ≤ |¬A| ∨ N = 0`):

  `(predicted_min A).re ≤ ((predicted_min A).re + (predicted_min ¬A).re)/2
   ↔ |A| ≤ |¬A| ∨ N = 0`

unconditionally. The extra `N = 0` branch handles the degenerate case
where both energies are 0.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pmA).re ≤ avg iff `|A| ≤ |¬A| ∨ N = 0`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_re_le_avg_complement_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  have hgap := bipartiteToyMinEnergyPredicted_re_sub_avg_complement_re_eq_biw_re
    (Λ := Λ) A N
  -- (pmA).re ≤ avg ↔ (pmA).re − avg ≤ 0 ↔ biw.re ≤ 0.
  have hequiv : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ↔
      (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hequiv]
  exact bipartiteImbalanceWeight_re_nonpos_iff (Λ := Λ) A N

end LatticeSystem.Quantum
