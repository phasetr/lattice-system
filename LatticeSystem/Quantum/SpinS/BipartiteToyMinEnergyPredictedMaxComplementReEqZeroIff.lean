import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmReEqZeroIff
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `max((pmA).re, (pm¬A).re) = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

PR #3084: `predictedSymm.re = 0 ↔ degenerate`.
PR #3001: `max = predictedSymm`.

Combining:

  `max((predicted_min A).re, (predicted_min ¬A).re) = 0
   ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **max(...) = 0 iff degenerate** (unconditional in `N`). Equivalent
to PR #3084 via PR #3001. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_eq_zero_iff_degenerate
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
        N = 0 := by
  rw [bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact bipartiteToyMinEnergyPredictedSymm_re_eq_zero_iff_degenerate (Λ := Λ) A N

end LatticeSystem.Quantum
