import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Sublattice-swap symmetry of orientation-pair max

  `max((pmA).re, (pm¬A).re) = max((pm(¬A)).re, (pm(¬(¬A))).re)`

unconditionally. After `¬¬A = A`, just `max_comm`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Sublattice-swap symmetry of orientation-pair max**. -/
theorem bipartiteToyMinEnergyPredicted_max_complement_re_sublattice_swap
    (A : Λ → Bool) (N : ℕ) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! ((fun y => ! A y) x)) N).re := by
  have hfun_eq : (fun x : Λ => ! ((fun y => ! A y) x)) = A := by funext x; simp
  rw [hfun_eq, max_comm]

end LatticeSystem.Quantum
