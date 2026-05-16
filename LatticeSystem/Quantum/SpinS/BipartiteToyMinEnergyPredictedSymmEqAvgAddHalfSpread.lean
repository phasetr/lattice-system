import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSymmSubAvgEqHalfSpread

/-!
# `(predictedSymm A).re = avg + ||A| − |¬A||·N / 2`

PR #3034: `(predictedSymm A).re − avg = ||A| − |¬A||·N / 2`.

Rearranging:

  `(predictedSymm A).re = ((predicted_min A).re + (predicted_min ¬A).re) / 2
    + ||A| − |¬A||·N / 2`

unconditionally. Explicit form of `predictedSymm` in terms of the
midpoint of the two orientation-specific predicted min energies and
the half-spread.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **predictedSymm via avg + half-spread**: rearrangement of PR #3034. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_eq_avg_add_half_spread
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 +
        |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
          (N : ℝ) / 2 := by
  have h := bipartiteToyMinEnergyPredictedSymm_re_sub_avg_complement_re_eq (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
