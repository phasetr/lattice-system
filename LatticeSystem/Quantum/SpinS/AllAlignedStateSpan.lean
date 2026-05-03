import LatticeSystem.Quantum.SpinS.AllAlignedStateLI

/-!
# Linear span of all-aligned states has dimension `N + 1`

For `[Nonempty V]`, the linear span of the all-aligned state
family has `Module.finrank ℂ` exactly `N + 1`.

Direct application of mathlib's `finrank_span_eq_card` to the
LI family of PR #957.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `Module.finrank ℂ (Submodule.span ℂ (Set.range allAlignedStateS))
= N + 1`. -/
theorem allAlignedStateS_span_finrank [Nonempty V] :
    Module.finrank ℂ
      (Submodule.span ℂ (Set.range
        (fun c : Fin (N + 1) =>
          (allAlignedStateS V N c : (V → Fin (N + 1)) → ℂ)))) =
      N + 1 := by
  have h := finrank_span_eq_card (R := ℂ)
    (b := fun c : Fin (N + 1) =>
      (allAlignedStateS V N c : (V → Fin (N + 1)) → ℂ))
    allAlignedStateS_linearIndependent
  simpa using h

end LatticeSystem.Quantum
