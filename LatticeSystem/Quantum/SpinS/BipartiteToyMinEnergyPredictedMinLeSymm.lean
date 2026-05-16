import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# Unconditional `min(...) ≤ (predictedSymm A).re`

PR #3001: `max((predicted_min A).re, (predicted_min ¬A).re) = (predictedSymm A).re`.

Since `min ≤ max` for any two reals, we get unconditionally:

  `min((predicted_min A).re, (predicted_min ¬A).re) ≤ (predictedSymm A).re`.

This is the weak version of PR #3016 (equality iff balanced) and
PR #3017 (strict iff unbalanced); it holds without any cardinality
or `N` hypothesis. Convenient as a one-step bound.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unconditional `min(...) ≤ (predictedSymm A).re`**: weak version
of PR #3016/#3017. Direct from PR #3001 (max = predictedSymm) and
`min ≤ max`. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_le_predictedSymm_re
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re ≤
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  exact min_le_max

end LatticeSystem.Quantum
