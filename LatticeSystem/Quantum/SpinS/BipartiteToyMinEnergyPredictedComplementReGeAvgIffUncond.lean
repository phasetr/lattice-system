import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementReSubAvgEqNegBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightReNonposIff

/-!
# `avg ≤ (pm¬A).re ↔ |A| ≤ |¬A| ∨ N = 0` unconditionally

Mirror of PR #3182. Combines PR #3158 (`(pm¬A).re − avg = −biw.re`)
with PR #3156 (`biw.re ≤ 0 ↔ |A| ≤ |¬A| ∨ N = 0`):

  `((predicted_min A).re + (predicted_min ¬A).re)/2 ≤ (predicted_min ¬A).re
   ↔ |A| ≤ |¬A| ∨ N = 0`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg ≤ (pm¬A).re iff `|A| ≤ |¬A| ∨ N = 0`** unconditionally. Mirror of PR #3182. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_ge_avg_complement_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ≤
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  have hgap := bipartiteToyMinEnergyPredicted_complement_re_sub_avg_complement_re_eq_neg_biw_re
    (Λ := Λ) A N
  -- avg ≤ (pm¬A).re ↔ 0 ≤ -biw.re ↔ biw.re ≤ 0.
  have hequiv : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ≤
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ↔
      (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hequiv]
  exact bipartiteImbalanceWeight_re_nonpos_iff (Λ := Λ) A N

end LatticeSystem.Quantum
