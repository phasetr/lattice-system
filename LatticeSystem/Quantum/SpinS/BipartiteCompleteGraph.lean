import LatticeSystem.Quantum.SpinS.ConfigDist
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The complete bipartite graph induced by a sublattice indicator
(Tasaki §2.5 Phase B-γ γ-3 final preparation)

For a vertex type `V` with a sublattice indicator `A : V → Bool`,
the **complete bipartite graph** `bipartiteCompleteGraphOf A` has
an edge between every pair of distinct vertices on different
sublattices:

  `(bipartiteCompleteGraphOf A).Adj x y ↔ x ≠ y ∧ A x ≠ A y`.

This is the natural "maximally connected" bipartite graph compatible
with the sublattice partition `(A^{-1}(true), A^{-1}(false))`. It is
the spin-S analogue setting where the Marshall–Lieb–Mattis irreducibility
argument is most cleanly stated: every bipartite raise/lower step
involves a `bipartiteCompleteGraphOf A`-edge, and conversely every
edge corresponds to a possible raise/lower step.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*}

/-- The complete bipartite graph induced by a sublattice indicator
`A : V → Bool`: an edge between `x` and `y` iff they are distinct
and lie on different sublattices. -/
@[simps]
def bipartiteCompleteGraphOf (A : V → Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ A x ≠ A y
  symm := fun _ _ ⟨h, hA⟩ => ⟨h.symm, fun heq => hA heq.symm⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- Adjacency in `bipartiteCompleteGraphOf A`: an edge iff distinct and
on different sublattices. -/
theorem bipartiteCompleteGraphOf_adj_iff (A : V → Bool) (x y : V) :
    (bipartiteCompleteGraphOf A).Adj x y ↔ x ≠ y ∧ A x ≠ A y :=
  Iff.rfl

/-- Every adjacency in `bipartiteCompleteGraphOf A` has endpoints
on different sublattices. -/
theorem bipartiteCompleteGraphOf_adj_sublattice_ne {A : V → Bool}
    {x y : V} (hadj : (bipartiteCompleteGraphOf A).Adj x y) :
    A x ≠ A y :=
  hadj.2

/-- Adjacency in `bipartiteCompleteGraphOf A` implies `x ≠ y`. -/
theorem bipartiteCompleteGraphOf_adj_ne {A : V → Bool}
    {x y : V} (hadj : (bipartiteCompleteGraphOf A).Adj x y) :
    x ≠ y :=
  hadj.1

/-- Decidability instance for adjacency in `bipartiteCompleteGraphOf A`,
useful for downstream computations (e.g. graph-derived couplings via
`couplingOf`). Relies on `DecidableEq V`. -/
instance bipartiteCompleteGraphOf_decidableAdj {V : Type*} [DecidableEq V]
    (A : V → Bool) :
    DecidableRel (bipartiteCompleteGraphOf A).Adj := by
  intro x y
  unfold bipartiteCompleteGraphOf SimpleGraph.Adj
  infer_instance

/-- The Marshall-trivial sublattice `A := fun _ => false` gives the
empty graph. -/
theorem bipartiteCompleteGraphOf_const_false {V : Type*} :
    bipartiteCompleteGraphOf (V := V) (fun _ => false) = ⊥ := by
  ext x y
  rw [bipartiteCompleteGraphOf_adj_iff]
  simp

/-- The Marshall-trivial sublattice `A := fun _ => true` gives the
empty graph. -/
theorem bipartiteCompleteGraphOf_const_true {V : Type*} :
    bipartiteCompleteGraphOf (V := V) (fun _ => true) = ⊥ := by
  ext x y
  rw [bipartiteCompleteGraphOf_adj_iff]
  simp

/-- For exactly-two-vertex `V` with the two vertices on different
sublattices, `bipartiteCompleteGraphOf A` has exactly the (single)
edge between them — a single edge graph. -/
theorem bipartiteCompleteGraphOf_adj_of_ne_of_sublattice_ne
    {A : V → Bool} {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y) :
    (bipartiteCompleteGraphOf A).Adj x y :=
  ⟨hxy, hAne⟩

/-! ## Bipartite step from over/under sites -/

variable [Fintype V] [DecidableEq V] {N : ℕ}

/-- For an over site `x` (where `(σ' x).val < (σ x).val`) and an
under site `y` (where `(σ y).val < (σ' y).val`) on different
sublattices (`A x ≠ A y`), there exists a configuration `σ''` reachable
from `σ` by a single bipartite raise/lower step (lower at `x`, raise
at `y`) such that `configDistS σ'' σ' + 2 = configDistS σ σ'`. -/
theorem exists_raiseLowerStepS_bipartite_of_over_under_ne_sublattice
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' := by
  -- Bounds for the raise/lower update.
  have hx_bound : (σ x).val - 1 < N + 1 := by
    have := (σ x).isLt; omega
  have hy_bound : (σ y).val + 1 < N + 1 := by
    have := (σ' y).isLt; omega
  -- Define σ''.
  let σ'' : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) y
      ⟨(σ y).val + 1, hy_bound⟩
  refine ⟨σ'', ?_, ?_⟩
  · -- Step σ ↦ σ'': lower at x, raise at y.
    -- Adjacency in the bipartite complete graph: x ≠ y and A x ≠ A y.
    have hadj : (bipartiteCompleteGraphOf A).Adj x y := ⟨hxy, hAne⟩
    -- σ'' agrees with σ off {x, y}.
    have hagree : ∀ k, k ≠ x → k ≠ y → σ'' k = σ k := by
      intro k hkx hky
      show (Function.update (Function.update σ x _) y _) k = σ k
      rw [Function.update_of_ne hky, Function.update_of_ne hkx]
    -- σ'' x and σ'' y values.
    have hupd_x : (σ'' x).val = (σ x).val - 1 := by
      show (Function.update (Function.update σ x _) y _ x).val = _
      rw [Function.update_of_ne hxy, Function.update_self]
    have hupd_y : (σ'' y).val = (σ y).val + 1 := by
      show (Function.update (Function.update σ x _) y _ y).val = _
      rw [Function.update_self]
    refine ⟨x, y, hadj, Or.inr ⟨?_, ?_⟩, hagree⟩
    · rw [hupd_x]; omega
    · rw [hupd_y]
  · -- Distance reduces by 2.
    exact configDistS_decrease_of_over_under hxy hover hunder

/-- The "hard case" of bipartite reachability: when over and under
sites land on the same sublattice, a 2-step transport through an
opposite-sublattice intermediate `z` (with `σ z < N` so it has room
to absorb a temporary +1) gives a `RaiseLowerReachableS` chain to a
configuration `σ''` with reduced `configDistS`.

The intermediate `σ_1` raises `z` then `σ_2 = σ''` lowers it back —
net effect on `z` is zero, and the (x, y) transport happens.

Hypothesis `hzN : (σ z).val < N` is needed for the raise step; the
existence of such `z` may fail in degenerate "saturated" configurations
but holds generically. -/
theorem exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAeq : A x = A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    {z : V} (hAz : A z ≠ A x) (hzN : (σ z).val < N) :
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
  have hz_raise_bound : (σ z).val + 1 < N + 1 := by omega
  -- Direct definition of σ_2 = σ with x lowered, y raised (z unchanged).
  let σ_2 : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) y
      ⟨(σ y).val + 1, hy_bound⟩
  -- Intermediate σ_1 = σ with x lowered, z raised.
  let σ_1 : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) z
      ⟨(σ z).val + 1, hz_raise_bound⟩
  -- σ_1 site values.
  have hσ_1_z : (σ_1 z).val = (σ z).val + 1 := by
    show (Function.update (Function.update σ x _) z _ z).val = _
    rw [Function.update_self]
  have hσ_1_x : (σ_1 x).val = (σ x).val - 1 := by
    show (Function.update (Function.update σ x _) z _ x).val = _
    rw [Function.update_of_ne hzx.symm, Function.update_self]
  have hσ_1_y_eq : σ_1 y = σ y := by
    show Function.update (Function.update σ x _) z _ y = σ y
    rw [Function.update_of_ne hzy.symm, Function.update_of_ne hxy.symm]
  have hσ_1_off : ∀ k, k ≠ x → k ≠ z → σ_1 k = σ k := by
    intro k hkx hkz
    show Function.update (Function.update σ x _) z _ k = σ k
    rw [Function.update_of_ne hkz, Function.update_of_ne hkx]
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
    -- Step 1: σ → σ_1 (lower x, raise z), edge (x, z).
    have hadj1 : (bipartiteCompleteGraphOf A).Adj x z :=
      ⟨hzx.symm, fun heq => hAz heq.symm⟩
    have hstep1 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ_1 := by
      refine ⟨x, z, hadj1, Or.inr ⟨?_, ?_⟩, hσ_1_off⟩
      · rw [hσ_1_x]; omega
      · rw [hσ_1_z]
    -- Step 2: σ_1 → σ_2 (lower z, raise y), edge (z, y).
    have hadj2 : (bipartiteCompleteGraphOf A).Adj z y :=
      ⟨hzy, fun heq => hAz (heq.trans hAeq.symm)⟩
    -- Differences σ_1 vs σ_2: at z (σ_1 z = σ z + 1, σ_2 z = σ z) and at y
    -- (σ_1 y = σ y, σ_2 y = σ y + 1). Off {z, y}: agree.
    have hagree2 : ∀ k, k ≠ z → k ≠ y → σ_2 k = σ_1 k := by
      intro k hkz hky
      by_cases hkx : k = x
      · subst hkx
        apply Fin.ext
        rw [hσ_1_x, hσ_2_x]
      · -- k ≠ x, k ≠ y, k ≠ z: σ_2 k = σ k = σ_1 k.
        rw [hσ_2_off k hkx hky, (hσ_1_off k hkx hkz).symm]
    -- Step 2 raise/lower data:
    -- (σ_2 z).val + 1 = (σ_1 z).val: σ_2 z = σ z, σ_1 z = σ z + 1. So σ z + 1 = σ z + 1 ✓.
    -- (σ_1 y).val + 1 = (σ_2 y).val: σ_1 y = σ y, σ_2 y = σ y + 1. So σ y + 1 = σ y + 1 ✓.
    have hupd_z2 : (σ_2 z).val + 1 = (σ_1 z).val := by
      have := hσ_2_z
      rw [show (σ_2 z).val = (σ z).val from by rw [this], hσ_1_z]
    have hupd_y2 : (σ_1 y).val + 1 = (σ_2 y).val := by
      rw [hσ_1_y_eq, hσ_2_y]
    have hstep2 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ_1 σ_2 := by
      refine ⟨z, y, hadj2, Or.inr ⟨hupd_z2, hupd_y2⟩, hagree2⟩
    -- Compose: σ → σ_1 → σ_2.
    exact (RaiseLowerReachableS.single hstep1).tail' hstep2
  · -- Distance reduction: σ_2 = direct lower-x raise-y at (x, y), so reduce by 2.
    exact configDistS_decrease_of_over_under hxy hover hunder

end LatticeSystem.Quantum
