import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphAltPath

/-!
# Structural bipartite over/under transport (no `h_intermediate`)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

This file provides the **structural** version of
`exists_raiseLowerReachableS_bipartite_of_over_under` that drops `h_intermediate`
entirely. Instead, it branches on whether the opposite-color site `z` has
`(σ z).val < N` (use original `_eq_sublattice`) or `(σ z).val > 0` (use
`_eq_sublattice_alt`). At any `N ≥ 1`, at least one of these holds for every
`σ z ∈ {0, 1, ..., N}`.

The new hypothesis: `hOppExists : ∃ z, A z ≠ A x` (just existence of opposite-
color site). This is automatically provable from `hA_ne + hB_ne` already in the
chain signature.

This is PR #3887.2 of the `h_intermediate` fix sequence.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} {N : ℕ}

/-- **Structural bipartite over/under transport (no `h_intermediate`)**.

For an over site `x` and under site `y` with `x ≠ y`, given an opposite-color
site `z` (`A z ≠ A x`), the reduction works at any `N ≥ 1` without further
constraints on `σ z`. Branches between the original path (uses `σ z < N`) and
the alternative path (uses `σ z > 0`), at least one of which is satisfied.

In the easy case `A x ≠ A y`, falls through to the direct step (no `z` needed).
In the hard case `A x = A y`, picks the path based on `σ z`. -/
theorem exists_raiseLowerReachableS_bipartite_of_over_under_structural
    [Fintype V] [DecidableEq V]
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    (hOppExists : A x = A y → ∃ z, A z ≠ A x)
    (hN : 1 ≤ N) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' := by
  by_cases hAeq : A x = A y
  · -- Hard case: same sublattice. Pick opposite-color z and branch on (σ z).val.
    obtain ⟨z, hAz⟩ := hOppExists hAeq
    -- At N ≥ 1, (σ z).val < N ∨ (σ z).val > 0.
    rcases lt_or_ge (σ z).val N with hzN | hzN
    · -- Original path: σ z < N.
      exact exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice
        hxy hAeq hover hunder hAz hzN
    · -- Alternative path: σ z ≥ N ≥ 1, so σ z > 0.
      have hzPos : 0 < (σ z).val := by omega
      exact exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice_alt
        hxy hAeq hover hunder hAz hzPos
  · -- Easy case: different sublattices, use direct step.
    obtain ⟨σ'', hstep, hreduce⟩ :=
      exists_raiseLowerStepS_bipartite_of_over_under_ne_sublattice
        hxy hAeq hover hunder
    exact ⟨σ'', RaiseLowerReachableS.single hstep, hreduce⟩

end LatticeSystem.Quantum
