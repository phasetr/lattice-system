import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubAvgEqBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightRePosIff

/-!
# `avg < (pmA).re ↔ |¬A| < |A| ∧ 0 < N` unconditionally

Strict dual of PR #3182. Combines PR #3157 (`(pmA).re − avg = biw.re`)
with PR #3151 (`0 < biw.re ↔ |¬A| < |A| ∧ 0 < N`):

  `((predicted_min A).re + (predicted_min ¬A).re)/2 < (predicted_min A).re
   ↔ |¬A| < |A| ∧ 0 < N`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg < (pmA).re iff `|¬A| < |A| ∧ 0 < N`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_re_gt_avg_complement_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 <
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card <
        (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < N := by
  have hgap := bipartiteToyMinEnergyPredicted_re_sub_avg_complement_re_eq_biw_re
    (Λ := Λ) A N
  -- avg < (pmA).re ↔ 0 < biw.re.
  have hequiv : ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 <
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ↔
      0 < (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hequiv]
  exact bipartiteImbalanceWeight_re_pos_iff (Λ := Λ) A N

end LatticeSystem.Quantum
