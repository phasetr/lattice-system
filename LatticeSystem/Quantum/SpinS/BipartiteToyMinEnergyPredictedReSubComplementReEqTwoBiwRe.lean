import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubAvgEqBiwRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedComplementReSubAvgEqNegBiwRe

/-!
# `(pmA).re − (pm¬A).re = 2 · biw.re` (signed spread)

Direct corollary of PRs #3157 and #3158: subtracting `(pm¬A).re − avg`
from `(pmA).re − avg` gives `(pmA).re − (pm¬A).re = biw.re − (−biw.re)
= 2 · biw.re`.

Signed companion of PR #3122 (`(pmA).re − (pm¬A).re` ↔ `spread =
2·‖biw‖`). The unsigned norm `‖biw‖` becomes the signed `biw.re`
here, which is positive on `|A| > |¬A|` and negative on `|A| < |¬A|`.

Also matches the existing PR #3021 (`(pmA).re − (pm¬A).re = (|A| − |¬A|)·N`)
via `2 · biw.re = 2 · (|A| − |¬A|)·N/2 = (|A| − |¬A|)·N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Signed spread: `(pmA).re − (pm¬A).re = 2 · biw.re`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq_two_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := bipartiteToyMinEnergyPredicted_re_sub_avg_complement_re_eq_biw_re
    (Λ := Λ) A N
  have h2 := bipartiteToyMinEnergyPredicted_complement_re_sub_avg_complement_re_eq_neg_biw_re
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
