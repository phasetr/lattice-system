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

end LatticeSystem.Quantum
