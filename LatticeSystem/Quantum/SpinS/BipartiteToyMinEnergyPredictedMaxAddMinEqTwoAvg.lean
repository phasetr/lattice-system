import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# `max(...) + min(...) = 2 · avg`

Generic identity: for any reals `x y`, `max x y + min x y = x + y`.
Applied to the orientation-pair:

  `max((pmA).re, (pm¬A).re) + min((pmA).re, (pm¬A).re) = 2 · avg`

where `avg = ((pmA).re + (pm¬A).re) / 2`. Unconditional.

Equivalent to PR #3031 (sum = max + min identity) in different form,
and consistent with PRs #3125/#3126 (max = avg + ‖biw‖, min = avg − ‖biw‖).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **max + min = 2 · avg** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_max_add_min_complement_re_eq_two_avg
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      2 * (((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2) := by
  have h := max_add_min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re
  linarith

end LatticeSystem.Quantum
