import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxSubLatticeSwap
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMinSubLatticeSwap

/-!
# Sublattice-swap symmetry of orientation-pair spread

PR #3119/#3120: max and min are sublattice-swap symmetric. Hence:

  `spread(A) = max(pmA, pm¬A) − min(pmA, pm¬A)
   = max(pm¬A, pmA) − min(pm¬A, pmA)
   = spread(¬A)`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Sublattice-swap symmetry of orientation-pair spread**. -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_sublattice_swap
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! ((fun y => ! A y) x)) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! ((fun y => ! A y) x)) N).re := by
  rw [← bipartiteToyMinEnergyPredicted_max_complement_re_sublattice_swap (Λ := Λ) A N,
      ← bipartiteToyMinEnergyPredicted_min_complement_re_sublattice_swap (Λ := Λ) A N]

end LatticeSystem.Quantum
