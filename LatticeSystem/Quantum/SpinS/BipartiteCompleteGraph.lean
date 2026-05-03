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

end LatticeSystem.Quantum
