import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubMinEqAbsSpread

/-!
# `min(...) = (predictedSymm A).re − ||A| − |¬A||·N`

PR #3015: `(predictedSymm A).re − min(...) = ||A| − |¬A||·N`.

Rearranged to solve for `min(...)`:

  `min((predicted_min A).re, (predicted_min ¬A).re)
   = (predictedSymm A).re − ||A| − |¬A||·N`

unconditionally. Explicit form of the min via `predictedSymm` minus
the orientation-spread. Complements PR #3001 (max = predictedSymm)
and PR #3011 (min via cardinality max/min) with a third explicit
form in terms of `predictedSymm` and the cardinality-gap absolute
value.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Explicit `min` via `predictedSymm` minus spread**:
`min(...) = (predictedSymm A).re − ||A| − |¬A||·N` unconditionally.
Direct rearrangement of PR #3015. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_predictedSymm_re_sub_spread
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
          (N : ℝ) := by
  have h := bipartiteToyMinEnergyPredictedSymm_re_sub_min_complement_re_eq (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
