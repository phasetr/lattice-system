import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic

/-!
# Bond-graph predicates for the Nagaoka connectivity criteria (Tasaki §11.2.2)

The graph-theoretic predicates on which Tasaki's two connectivity criteria
(Theorem 11.8 and Lemma 11.9, stated in `NagaokaConnectivityClassification.lean`)
are formulated: the bond graph of a hopping amplitude, biconnectedness, the
simple-loop predicate, exchange bonds (E1: a common length-3/4 loop; E2: deleting
the pair keeps the graph connected), the exchange-bond graph, and connectivity by
exchange bonds.  They live in their own module so that the proof machinery
(`NagaokaStateQuiver.lean`) can use them without importing the Theorem 11.8
axiom, and the statements module can in turn import the proof machinery.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, pp. 386–388.
-/

namespace LatticeSystem.Fermion

/-- The **bond graph** `(Λ, B)` of a hopping amplitude: an edge `x — y` whenever
`x ≠ y` and the hopping `t_{x,y}` (or its transpose) is non-zero.  The symmetric
closure is taken so the definition is a `SimpleGraph` without assuming
`t_{x,y} = t_{y,x}` (for symmetric `t` it is just the support of `t`). -/
def nagaokaBondGraph (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) :
    SimpleGraph (Fin (N + 1)) where
  Adj x y := x ≠ y ∧ (t x y ≠ 0 ∨ t y x ≠ 0)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- A graph is **biconnected** (non-separable) if it is connected and removing
any single vertex leaves it connected — there is no cut vertex.  (Tasaki fn. 10,
§11.2.2.)  The `G.Connected` conjunct excludes degenerate disconnected graphs
(e.g. isolated vertices), for which "delete any vertex stays connected" would
otherwise hold vacuously. -/
def IsBiconnected {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, (G.induce {w | w ≠ v}).Connected

/-- A graph is a **simple loop with more than four sites** if it is isomorphic to
the cycle graph `C_n` for some `n > 4` (a periodic chain on `≥ 5` sites). -/
def IsSimpleLoopGTFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, 4 < n ∧ Nonempty (G ≃g SimpleGraph.cycleGraph n)

/-- A pair `{x, y}` is an **exchange bond** of a graph `G` when (E1) `x` and `y`
lie on a common loop (cycle) of length 3 or 4, and (E2) `G` stays connected when
both `x` and `y` are removed.  (Tasaki §11.2.2, definition before Lemma 11.9.) -/
def IsExchangeBond {V : Type*} (G : SimpleGraph V) (x y : V) : Prop :=
  (∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ (c.length = 3 ∨ c.length = 4) ∧
      x ∈ c.support ∧ y ∈ c.support) ∧
    (G.induce {w | w ≠ x ∧ w ≠ y}).Connected

/-- The **exchange-bond graph**: an edge `x — y` whenever `{x, y}` (or `{y, x}`)
is an exchange bond.  The symmetric closure of `IsExchangeBond` (which is itself
symmetric in `x, y`) is taken so the definition is a `SimpleGraph` without a
separate symmetry proof. -/
def exchangeBondGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (IsExchangeBond G x y ∨ IsExchangeBond G y x)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- A graph is **connected by exchange bonds** when its exchange-bond graph is
connected. -/
def ConnectedByExchangeBonds {V : Type*} (G : SimpleGraph V) : Prop :=
  (exchangeBondGraph G).Connected

end LatticeSystem.Fermion
