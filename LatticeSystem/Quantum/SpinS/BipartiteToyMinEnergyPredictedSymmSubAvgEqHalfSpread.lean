import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedAvgComplementRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe

/-!
# `(predictedSymm A).re − avg = ||A| − |¬A||·N / 2`

PR #3001: `max((pmA).re, (pm¬A).re) = (predictedSymm A).re`.
PR #3033: `avg = (max + min)/2 = -|A|·|¬A|·N²/2 − |Λ|·N/2`.
PR #3012: `max − min = ||A| − |¬A||·N`.

Hence `predictedSymm − avg = max − (max + min)/2 = (max − min)/2 =
||A| − |¬A||·N / 2`:

  `(predictedSymm A).re − ((pmA).re + (pm¬A).re) / 2
   = ||A| − |¬A||·N / 2`

unconditionally. **Half-spread separation**: the symmetric Tasaki
§2.5 Theorem 2.3 prediction sits exactly half the orientation-spread
above the arithmetic mean of the two orientation-specific predicted
min energies.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Half-spread separation**: `(predictedSymm A).re − avg =
||A| − |¬A||·N / 2`. Direct from PR #3001 (max = predictedSymm) +
PR #3012 (spread) + `max_add_min` identity. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_sub_avg_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re -
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) / 2 := by
  -- predictedSymm = max, sum = max + min, so predictedSymm − sum/2 = max − (max+min)/2 = (max−min)/2.
  have hmax_eq_symm :=
    bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re (Λ := Λ) A N
  have hsum : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    (max_add_min _ _).symm
  rw [← hmax_eq_symm, hsum]
  have hdiff := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
