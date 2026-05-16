import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyNonpos

/-!
# `avg ≤ 0` unconditionally

Direct from PR #2791 (`(pmA).re ≤ 0`) applied to both orientations:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2 ≤ 0`

unconditionally. Since both orientation-specific predicted min
energies are non-positive (PR #2791 applied to A and ¬A), their
arithmetic mean is also non-positive.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`avg ≤ 0`** unconditional. Both orientations are non-positive
(PR #2791), so their average is. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_le_zero
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 ≤ 0 := by
  have hA := bipartiteToyMinEnergyPredicted_re_nonpos (Λ := Λ) A N
  have hB := bipartiteToyMinEnergyPredicted_re_nonpos (Λ := Λ) (fun x => ! A x) N
  linarith

end LatticeSystem.Quantum
