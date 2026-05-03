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
at `y`) such that `configDistS σ'' σ' + 2 = configDistS σ σ'`.

This is the "easy case" of bipartite reachability: when the witness
sites land on different sublattices, the bipartite complete graph
contains the required edge directly. The "hard case" (witness sites
on the same sublattice) requires a 2-step transport through an
opposite-sublattice intermediate. -/
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

end LatticeSystem.Quantum
