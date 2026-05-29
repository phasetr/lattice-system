import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph

/-!
# Alternative bipartite over/under transport (lower-z path)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

This file provides the **alternative path** for the same-sublattice over/under
case in `exists_raiseLowerReachableS_bipartite_of_over_under`. The original path
(`exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice`,
`LatticeSystem/Quantum/SpinS/BipartiteCompleteGraph.lean:152`) requires
`(σ z).val < N` (z raisable). The alternative requires `(σ z).val > 0` (z
lowerable).

At any `N ≥ 1`, every opposite-color site `z` satisfies **at least one** of
these two conditions, so a structural fix (branching) can drop `h_intermediate`
entirely.

This is the first PR (#3887.1) of the `h_intermediate` fix sequence — adds the
alternative lemma; downstream PRs will branch and refactor the chain.

## Path comparison

| Step | Original (`σ z < N`) | Alternative (`σ z > 0`) |
|---|---|---|
| 1 | lower x + raise z (edge x-z) | raise y + lower z (edge y-z) |
| 2 | lower z + raise y (edge z-y) | lower x + raise z (edge x-z) |
| Final | `σ_2` = `lower x, raise y` | `σ_2` = `lower x, raise y` |

Both reach the same `σ_2`; they differ in which condition on `σ z` is needed.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Function

variable {V : Type*} {N : ℕ}

/-- **Alternative bipartite over/under transport (same sublattice, lower-z path)**.

For an over site `x` and under site `y` with `A x = A y` (same sublattice),
`x ≠ y`, `σ x > σ' x` (over) and `σ y < σ' y` (under), if an opposite-color
site `z` exists with `(σ z).val > 0` (z lowerable), then `σ_2 = (lower x,
raise y)` is reachable in 2 steps via the path `σ → σ_1 → σ_2` where
`σ_1 = (raise y, lower z)` (step 1: y-z edge) and `σ_2 = (lower x, raise z)`
applied to `σ_1` (step 2: x-z edge).

Mirror of `exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice`
with the `σ z` condition flipped. -/
theorem exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice_alt
    [Fintype V] [DecidableEq V]
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAeq : A x = A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    {z : V} (hAz : A z ≠ A x) (hzPos : 0 < (σ z).val) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' := by
  -- z ≠ x, z ≠ y (since A z ≠ A x = A y).
  have hzx : z ≠ x := fun heq => hAz (heq ▸ rfl)
  have hzy : z ≠ y := fun heq => hAz (heq ▸ hAeq.symm)
  -- Bounds for the updates.
  have hx_bound : (σ x).val - 1 < N + 1 := by
    have := (σ x).isLt; omega
  have hy_bound : (σ y).val + 1 < N + 1 := by
    have := (σ' y).isLt; omega
  have hz_lower_bound : (σ z).val - 1 < N + 1 := by
    have := (σ z).isLt; omega
  -- σ_2 = σ with x lowered, y raised (z unchanged).
  let σ_2 : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) y
      ⟨(σ y).val + 1, hy_bound⟩
  -- Intermediate σ_1 = σ with y raised, z lowered (x unchanged).
  let σ_1 : V → Fin (N + 1) :=
    Function.update (Function.update σ y ⟨(σ y).val + 1, hy_bound⟩) z
      ⟨(σ z).val - 1, hz_lower_bound⟩
  -- σ_1 site values.
  have hσ_1_z : (σ_1 z).val = (σ z).val - 1 := by
    show (Function.update (Function.update σ y _) z _ z).val = _
    rw [Function.update_self]
  have hσ_1_y : (σ_1 y).val = (σ y).val + 1 := by
    show (Function.update (Function.update σ y _) z _ y).val = _
    rw [Function.update_of_ne hzy.symm, Function.update_self]
  have hσ_1_x_eq : σ_1 x = σ x := by
    show Function.update (Function.update σ y _) z _ x = σ x
    rw [Function.update_of_ne hzx.symm, Function.update_of_ne hxy]
  have hσ_1_off : ∀ k, k ≠ y → k ≠ z → σ_1 k = σ k := by
    intro k hky hkz
    show Function.update (Function.update σ y _) z _ k = σ k
    rw [Function.update_of_ne hkz, Function.update_of_ne hky]
  -- σ_2 site values.
  have hσ_2_x : (σ_2 x).val = (σ x).val - 1 := by
    show (Function.update (Function.update σ x _) y _ x).val = _
    rw [Function.update_of_ne hxy, Function.update_self]
  have hσ_2_y : (σ_2 y).val = (σ y).val + 1 := by
    show (Function.update (Function.update σ x _) y _ y).val = _
    rw [Function.update_self]
  have hσ_2_z : σ_2 z = σ z := by
    show (Function.update (Function.update σ x _) y _) z = σ z
    rw [Function.update_of_ne hzy, Function.update_of_ne hzx]
  have hσ_2_off : ∀ k, k ≠ x → k ≠ y → σ_2 k = σ k := by
    intro k hkx hky
    show (Function.update (Function.update σ x _) y _) k = σ k
    rw [Function.update_of_ne hky, Function.update_of_ne hkx]
  refine ⟨σ_2, ?_, ?_⟩
  · -- Reachability via 2 steps σ → σ_1 → σ_2.
    -- Step 1: σ → σ_1 (raise y, lower z), edge (y, z).
    have hadj1 : (bipartiteCompleteGraphOf A).Adj y z := by
      refine ⟨hzy.symm, ?_⟩
      intro heq
      exact hAz (heq.symm.trans hAeq.symm)
    -- For the step we need: lower one and raise the other. y is raised, z is lowered.
    have hstep1_raise_y : (σ y).val + 1 = (σ_1 y).val := by rw [hσ_1_y]
    have hstep1_lower_z : (σ_1 z).val + 1 = (σ z).val := by rw [hσ_1_z]; omega
    have hstep1 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ_1 := by
      refine ⟨z, y, ?_, Or.inr ⟨?_, ?_⟩, ?_⟩
      · -- adj z y
        refine ⟨hzy, ?_⟩
        intro heq
        exact hAz (heq.trans hAeq.symm)
      · -- (σ z).val = (σ_1 z).val + 1
        rw [hσ_1_z]; omega
      · -- (σ_1 y).val = (σ y).val + 1
        rw [hσ_1_y]
      · -- off-{z, y} agreement (for RaiseLowerStepS the agreement direction
        -- is σ k = σ_1 k since z is "lower" side and y is "raise" side,
        -- with the step lowering z and raising y).
        intro k hkz hky
        exact (hσ_1_off k hky hkz)
    -- Step 2: σ_1 → σ_2 (lower x, raise z back).
    -- σ_1: x unchanged (= σ x), y raised, z lowered.
    -- σ_2: x lowered, y raised (= σ_1 y), z unchanged from σ (= σ_1 z + 1).
    -- Difference σ_1 → σ_2: x lowered by 1, z raised by 1.
    have hagree2 : ∀ k, k ≠ x → k ≠ z → σ_2 k = σ_1 k := by
      intro k hkx hkz
      by_cases hky : k = y
      · subst hky
        apply Fin.ext
        rw [hσ_1_y, hσ_2_y]
      · -- k ≠ x, k ≠ y, k ≠ z: σ_2 k = σ k = σ_1 k.
        rw [hσ_2_off k hkx hky, (hσ_1_off k hky hkz).symm]
    have hadj2 : (bipartiteCompleteGraphOf A).Adj x z :=
      ⟨hzx.symm, fun heq => hAz heq.symm⟩
    have hupd_x2 : (σ_2 x).val + 1 = (σ_1 x).val := by
      rw [hσ_2_x]
      have hσ_1_x_val : (σ_1 x).val = (σ x).val := by rw [hσ_1_x_eq]
      rw [hσ_1_x_val]; omega
    have hupd_z2 : (σ_1 z).val + 1 = (σ_2 z).val := by
      have h2 : (σ_2 z).val = (σ z).val := by rw [hσ_2_z]
      have h1 : (σ_1 z).val = (σ z).val - 1 := hσ_1_z
      omega
    have hstep2 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ_1 σ_2 := by
      refine ⟨x, z, hadj2, Or.inr ⟨hupd_x2, hupd_z2⟩, hagree2⟩
    -- Compose: σ → σ_1 → σ_2.
    exact (RaiseLowerReachableS.single hstep1).tail' hstep2
  · -- Distance reduction: σ_2 = direct lower-x raise-y at (x, y), so reduce by 2.
    exact configDistS_decrease_of_over_under hxy hover hunder

end LatticeSystem.Quantum
