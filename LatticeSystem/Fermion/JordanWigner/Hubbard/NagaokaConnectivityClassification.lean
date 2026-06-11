import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity condition: classification (Tasaki §11.2.2, Theorem 11.8 and Lemma 11.9)

After **Definition 11.6** (`nagaokaConnectivity`) and **Theorem 11.7**
(`nagaoka_theorem_11_7`, proven in `NagaokaConnectivity.lean`), Tasaki §11.2.2
gives two criteria for *verifying* the connectivity condition on a concrete
bond graph `(Λ, B)`, `B = {{x, y} : t_{x,y} ≠ 0}`:

* **Theorem 11.8** (Bobrow–Stubis–Li): the connectivity condition holds *iff*
  `(Λ, B)` is biconnected and is not a simple loop (periodic chain) with more
  than four sites.
* **Lemma 11.9**: if `(Λ, B)` is connected by *exchange bonds*, the connectivity
  condition holds.

## Status

* **Theorem 11.8** is recorded as an **`axiom`**: Tasaki's text *explicitly
  leaves the proof to the original papers* — Bobrow, Stubis and Li, and Wilson's
  graph-theoretic analysis of the "15-puzzle" (Tasaki 1st ed., §11.2.2, p. 387,
  refs [4], [81]). The book itself provides no proof, so it is a *cited external
  classification theorem*. Rather than reproduce Wilson's theorem we axiomatize
  its statement.

* **Lemma 11.9** was initially axiomatized here (project decision, 2026-06-04)
  and is now a **proved theorem** `nagaoka_lemma_11_9` in
  `NagaokaStateQuiver.lean`, which turns Tasaki's "15-puzzle" hole-motion proof
  into strong connectivity of the per-sector quiver of `−M` (loop-trip spin
  swaps, exchange-bond generation, hole parking, mismatch reduction). This file
  keeps the *predicates* (`nagaokaBondGraph`, `IsExchangeBond`,
  `exchangeBondGraph`, `ConnectedByExchangeBonds`) on which both results are
  stated.

**Theorem 11.7 itself (`NagaokaConnectivity.lean`) is `sorry`-free and does not
depend on the Theorem 11.8 axiom** — it is isolated in this file so that the
proven core stays axiom-clean.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.8 and Lemma 11.9, pp. 386–388.
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

/-- **Tasaki Theorem 11.8 (necessary and sufficient condition for connectivity).**
A Hubbard model with `U = ∞`, `N = |Λ| − 1` and `t ≥ 0` satisfies the
connectivity condition (Definition 11.6, `nagaokaConnectivity`) if and only if
its bond graph is biconnected and is not a simple loop with more than four sites.

**AXIOMATIZED (deferred to future implementation).**  Tasaki leaves the proof to
Bobrow–Stubis–Li and Wilson's "15-puzzle" theorem (1st ed., §11.2.2, p. 387,
refs [4], [81]); the book gives no proof, so this is a cited external
classification result.  See the module docstring for the rationale.  (`1 ≤ N`
excludes the degenerate single-site case, where there are no electrons to order.)
-/
axiom nagaoka_theorem_11_8 (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hN : 1 ≤ N) (htsym : ∀ i j, t i j = t j i) (hpos : ∀ i j, 0 ≤ t i j) :
    nagaokaConnectivity N t ↔
      (IsBiconnected (nagaokaBondGraph N t) ∧
        ¬ IsSimpleLoopGTFour (nagaokaBondGraph N t))

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

/-! **Tasaki Lemma 11.9 (a sufficient condition for connectivity)** — formerly an `axiom` here —
is now a **proved theorem** `nagaoka_lemma_11_9` in `NagaokaStateQuiver.lean`, which builds the
full "15-puzzle" hole-motion argument (loop-trip spin swaps, exchange-bond generation, hole
parking, and mismatch reduction) on top of the predicates defined in this file. -/

end LatticeSystem.Fermion
