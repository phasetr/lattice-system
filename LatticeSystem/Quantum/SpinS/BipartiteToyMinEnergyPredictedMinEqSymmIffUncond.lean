import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadEqZeroIffUncond
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxEqPredictedSymm

/-!
# `min(...) = (predictedSymm A).re ↔ |A| = |¬A| ∨ N = 0` unconditionally

PR #3090: `spread = 0 ↔ balanced ∨ N = 0` unconditionally.
PR #3001: `max = predictedSymm`.

`spread = max − min = 0 ↔ max = min`. Substituting:

  `min((pmA).re, (pm¬A).re) = (predictedSymm A).re
   ↔ |A| = |¬A| ∨ N = 0`.

Unconditional version of PR #3016 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **min = predictedSymm iff balanced ∨ N = 0** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_min_complement_re_eq_predictedSymm_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∨
      N = 0 := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_eq_predictedSymm_re A N]
  -- Goal: min = max ↔ balanced ∨ N = 0.
  -- min = max ↔ max - min = 0 (in reals), then apply PR #3090.
  rw [show (min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) ↔
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re = 0
      from by constructor <;> intro h <;> linarith]
  exact bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_zero_iff_balanced_or_N_zero
    (Λ := Λ) A N

end LatticeSystem.Quantum
