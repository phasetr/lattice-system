import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgSubMinEqHalfSpread

/-!
# `min((pmA).re, (pm¬A).re) = avg − ||A| − |¬A||·N / 2`

PR #3039: `avg − min = ||A| − |¬A||·N / 2`.

Rearranging to solve for `min`:

  `min((predicted_min A).re, (predicted_min ¬A).re)
   = ((predicted_min A).re + (predicted_min ¬A).re) / 2
       − ||A| − |¬A||·N / 2`

unconditionally. Mirror of PR #3043 (`predictedSymm = avg +
half_spread`) for the lower end of the orientation sandwich.
Explicit form of the orientation min in terms of the midpoint and
the half-spread.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min via avg − half-spread**: mirror of PR #3043. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_avg_sub_half_spread
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 -
        |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
          (N : ℝ) / 2 := by
  have h := bipartiteToyMinEnergyPredicted_avg_complement_re_sub_min_eq (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
