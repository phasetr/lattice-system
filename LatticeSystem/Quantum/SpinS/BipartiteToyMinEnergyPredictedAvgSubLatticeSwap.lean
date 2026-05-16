import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Sublattice-swap symmetry of the orientation-pair average

`avg(A)` and `avg(¬A)` involve the same pair `{(pmA).re, (pm¬A).re}`
(in different order), so they're equal:

  `((pmA).re + (pm¬A).re) / 2
   = ((pm(¬A)).re + (pm(¬(¬A))).re) / 2`

unconditionally. After functional simplification `¬¬A = A`, this is
just `add_comm`. Reflects the convention-independence of which
sublattice is labelled "A" in the orientation-pair framework.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Sublattice-swap symmetry of `avg`**: `avg(A) = avg(¬A)`
unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_sublattice_swap
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      ((bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! ((fun y => ! A y) x)) N).re) / 2 := by
  -- (¬¬A) = A pointwise, so the second predicted_min reduces to (pmA).
  have hfun_eq : (fun x : Λ => ! ((fun y => ! A y) x)) = A := by funext x; simp
  rw [hfun_eq, add_comm]

end LatticeSystem.Quantum
