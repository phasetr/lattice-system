import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphAltPath
import LatticeSystem.Quantum.SpinS.ParityReachableWithinSector
import LatticeSystem.Quantum.SpinS.ParityReachToMinMagSum
import LatticeSystem.Quantum.SpinS.ParityReachableSymm
import LatticeSystem.Quantum.SpinS.ParityReachableMagSum

/-!
# Structural bipartite over/under transport (no `h_intermediate`)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

This file provides the **structural** version of
`exists_raiseLowerReachableS_bipartite_of_over_under_legacy` that drops `h_intermediate`
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

set_option linter.unusedDecidableInType false in
/-- **Structural bipartite over/under transport (no `h_intermediate`)**.

For an over site `x` and under site `y` with `x ≠ y`, given an opposite-color
site `z` (`A z ≠ A x`), the reduction works at any `N ≥ 1` without further
constraints on `σ z`. Branches between the original path (uses `σ z < N`) and
the alternative path (uses `σ z > 0`), at least one of which is satisfied.

In the easy case `A x ≠ A y`, falls through to the direct step (no `z` needed).
In the hard case `A x = A y`, picks the path based on `σ z`. -/
theorem exists_raiseLowerReachableS_bipartite_of_over_under
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

/-! ## Structural within-sector reachability -/

/-- Opposite-color site existence from `hA_ne + hB_ne`: if `A x = A y`, then any
opposite-color site (of A x) can be obtained from either `hA_ne` or `hB_ne`. -/
theorem oppExists_of_hA_hB
    (A : V → Bool) (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (x : V) :
    ∃ z, A z ≠ A x := by
  rcases hAx : A x with _ | _
  · obtain ⟨a, ha⟩ := hA_ne; exact ⟨a, by simp [ha]⟩
  · obtain ⟨b, hb⟩ := hB_ne; exact ⟨b, by simp [hb]⟩

set_option linter.unusedDecidableInType false in
/-- **Structural within-sector reachability (no `h_intermediate`)**: for any two
same-magnetization configurations of the same complete bipartite graph,
`RaiseLowerReachableS` connects them, using only `hA_ne + hB_ne + 1 ≤ N`. -/
theorem raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS
    [Fintype V] [DecidableEq V]
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)} (hmag : magSumS σ = magSumS σ') :
    RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  -- Strong induction on configDistS σ σ'.
  suffices h : ∀ n, ∀ σ σ' : V → Fin (N + 1),
      magSumS σ = magSumS σ' → configDistS σ σ' ≤ n →
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ' from
    h (configDistS σ σ') σ σ' hmag (le_refl _)
  intro n
  induction n with
  | zero =>
    intro σ σ' _ hd
    have hsigma : σ = σ' :=
      (configDistS_eq_zero_iff σ σ').mp (Nat.le_zero.mp hd)
    rw [hsigma]
    exact RaiseLowerReachableS.refl _ _
  | succ n ih =>
    intro σ σ' hmag hd
    by_cases hne : σ = σ'
    · rw [hne]; exact RaiseLowerReachableS.refl _ _
    · obtain ⟨⟨x, hover⟩, y, hunder⟩ :=
        exists_over_under_of_eq_magSumS hne hmag
      have hxy : x ≠ y := fun heq => by subst heq; omega
      -- Provide hOppExists from hA_ne + hB_ne.
      have hOppExists : A x = A y → ∃ z, A z ≠ A x :=
        fun _ => oppExists_of_hA_hB A hA_ne hB_ne x
      obtain ⟨σ_2, hreach, hreduce⟩ :=
        exists_raiseLowerReachableS_bipartite_of_over_under
          hxy hover hunder hOppExists hN
      have hmag_2 : magSumS σ_2 = magSumS σ :=
        magSumS_eq_of_raiseLowerReachableS hreach
      have hIH : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ_2 σ' := by
        apply ih
        · rw [hmag_2]; exact hmag
        · omega
      exact hreach.trans hIH

/-! ## Structural `parityReachableS` totality -/

set_option linter.unusedDecidableInType false in
/-- **Structural `ParityReachableS` totality (no `h_intermediate`)**: any two
configurations of the same total-magnetization parity are connected, using only
`hA_ne + hB_ne + 1 ≤ N`. -/
theorem parityReachableS_total
    [Fintype V] [DecidableEq V]
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    parityReachableS_to_min_magSum A hA_ne hB_ne σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    parityReachableS_to_min_magSum A hA_ne hB_ne σ'
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq h_reach_min
    have h2 := parityReachableS_magSumS_parity_eq h'_reach_min
    omega
  have h_within :=
    parityReachableS_of_raiseLowerReachableS
      (raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS
        A hA_ne hB_ne hN h_par_min)
  have h_back := parityReachableS_symm h'_reach_min
  exact (h_reach_min.trans h_within).trans h_back

end LatticeSystem.Quantum
