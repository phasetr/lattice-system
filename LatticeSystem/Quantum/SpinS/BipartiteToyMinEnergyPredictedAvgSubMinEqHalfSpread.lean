import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubMinComplementRe
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `avg − min = ||A| − |¬A||·N / 2`

PR #3012: `max − min = ||A| − |¬A||·N`.

Since `avg = (max + min)/2`, we have `avg − min = (max − min)/2 =
||A| − |¬A||·N / 2`:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2
    − min((predicted_min A).re, (predicted_min ¬A).re)
   = ||A| − |¬A||·N / 2`

unconditionally. Mirror of PR #3034 (`predictedSymm − avg =
||A| − |¬A||·N/2`): the average sits exactly half the
orientation-spread above the minimum.

Together with PR #3034, this gives the symmetric sandwich:
`predictedSymm − avg = avg − min = ||A| − |¬A||·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **avg − min = half-spread**: mirror of PR #3034. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_sub_min_eq
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) / 2 := by
  have hsum : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    (max_add_min _ _).symm
  rw [hsum]
  have hdiff := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
