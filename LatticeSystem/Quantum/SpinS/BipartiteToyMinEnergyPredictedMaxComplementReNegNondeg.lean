import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmStrictNeg

/-!
# `max(...) < 0` at non-degenerate

PR #3001: `max((pmA).re, (pm¬A).re) = (predictedSymm A).re`.
PR #2845: `(predictedSymm A).re < 0` at `|A| ≥ 1, |¬A| ≥ 1, N ≥ 1`.

Combining:

  `0 < |A|, 0 < |¬A|, 0 < N
    → max((predicted_min A).re, (predicted_min ¬A).re) < 0`.

Strict version of PR #3030 (unconditional `max ≤ 0`). Equivalent to
PR #2845 via PR #3001 but stated in `max` form for direct use.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max((pmA).re, (pm¬A).re) < 0` at non-degenerate**. Strict version
of PR #3030; equivalent to PR #2845 via PR #3001. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_neg_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re < 0 := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact bipartiteToyMinEnergyPredictedSymm_re_neg_of_nondegenerate
    (Λ := Λ) (A := A) (N := N) hA hAc hN

end LatticeSystem.Quantum
