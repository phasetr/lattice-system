import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.ZMod.Basic
import LatticeSystem.Lattice.Graph

/-!
# The hexagonal (honeycomb) lattice on a torus

This module fixes the **graph-centric** datum underlying Tasaki's Theorem 7.7: the
hexagonal lattice, realized as a finite torus, is the concrete graph on which the
`S = 3/2` (`N = 3`) AKLT model lives (Tasaki §7.3.2, eq. (7.3.8), p. 211).  Tasaki's
footnote 42 (p. 211) stresses that periodic boundary conditions are chosen so that the
lattice stays **bipartite**; this is exactly the structure formalized here.

The honeycomb lattice is built from the square torus `ZMod m × ZMod m` with a two-site
brick-wall unit cell (`Bool` = the two sublattices `A`/`B`).  An `A`-site in cell `(p, q)`
is joined to the three `B`-sites in cells `(p, q)`, `(p - 1, q)` and `(p, q - 1)` — the
three honeycomb bond directions — so every vertex has coordination number `3`
(coordination number `3` ⇒ uniform spin `S = 3/2`).

It provides, with no quantum / C*-algebra dependencies:

* `honeycombTorusGraph m : SimpleGraph ((ZMod m × ZMod m) × Bool)` — the honeycomb torus
  as a `SimpleGraph`, together with `DecidableRel` on its adjacency;
* `honeycombTorusGraph_isRegularOfDegree` — every vertex has degree `3` (for `2 ≤ m`,
  which rules out the small-torus degeneracies where the three neighbours collide);
* `honeycombTorusGraph_isBipartiteWith` / `honeycombTorusGraph_isBipartite` — the
  `A`/`B` sublattices are a bipartition (Tasaki footnote 42, p. 211).

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §7.3.2, eq. (7.3.8) and Theorem 7.7, footnote 42, pp. 210–211.
-/

namespace LatticeSystem.Lattice

variable (m : ℕ)

/-- The **honeycomb bond relation** between two unit cells `a` (an `A`-cell) and `b`
(a `B`-cell) of the torus `ZMod m × ZMod m`: `b` is one of the three cells `a`,
`(a.1 - 1, a.2)`, `(a.1, a.2 - 1)` reached by the three honeycomb bond directions from an
`A`-site (Tasaki eq. (7.3.8), p. 211). -/
def honeycombBond {m : ℕ} (a b : ZMod m × ZMod m) : Prop :=
  b = a ∨ b = (a.1 - 1, a.2) ∨ b = (a.1, a.2 - 1)

instance {m : ℕ} (a b : ZMod m × ZMod m) : Decidable (honeycombBond a b) := by
  unfold honeycombBond; infer_instance

/-- The **hexagonal (honeycomb) lattice on the torus** `ZMod m × ZMod m` with a two-site
brick-wall unit cell (`Bool` = the `A`/`B` sublattice).  Two vertices are adjacent iff they
lie in opposite sublattices and their cells are joined by one of the three honeycomb bond
directions (`honeycombBond`).  This is the 3-regular bipartite lattice of Tasaki's `S = 3/2`
AKLT model (§7.3.2, eq. (7.3.8), p. 211). -/
def honeycombTorusGraph (m : ℕ) : SimpleGraph ((ZMod m × ZMod m) × Bool) where
  Adj v w :=
    (v.2 = false ∧ w.2 = true ∧ honeycombBond v.1 w.1) ∨
      (v.2 = true ∧ w.2 = false ∧ honeycombBond w.1 v.1)
  symm := by
    rintro v w (⟨hv, hw, hb⟩ | ⟨hv, hw, hb⟩)
    · exact Or.inr ⟨hw, hv, hb⟩
    · exact Or.inl ⟨hw, hv, hb⟩
  loopless := ⟨by rintro v (⟨hv, hw, -⟩ | ⟨hv, hw, -⟩) <;> simp_all⟩

variable {m}

/-- Adjacency in `honeycombTorusGraph m` unfolds to the honeycomb bond condition: the two
endpoints lie in opposite sublattices and their cells are `honeycombBond`-related. -/
theorem honeycombTorusGraph_adj {v w : (ZMod m × ZMod m) × Bool} :
    (honeycombTorusGraph m).Adj v w ↔
      (v.2 = false ∧ w.2 = true ∧ honeycombBond v.1 w.1) ∨
        (v.2 = true ∧ w.2 = false ∧ honeycombBond w.1 v.1) :=
  Iff.rfl

instance : DecidableRel (honeycombTorusGraph m).Adj := fun v w =>
  decidable_of_iff _ (honeycombTorusGraph_adj (v := v) (w := w)).symm

variable (m)

/-! ### Bipartite structure: the `A`/`B` sublattices -/

/-- The **`A`-sublattice** `{v : v.2 = false}` (first color class of the bipartition). -/
def honeycombSublatticeA : Set ((ZMod m × ZMod m) × Bool) := {v | v.2 = false}

/-- The **`B`-sublattice** `{v : v.2 = true}` (second color class of the bipartition). -/
def honeycombSublatticeB : Set ((ZMod m × ZMod m) × Bool) := {v | v.2 = true}

/-- The honeycomb torus is **bipartite with the `A`/`B` sublattices** as the two parts:
every bond joins an `A`-site to a `B`-site (Tasaki footnote 42, p. 211). -/
theorem honeycombTorusGraph_isBipartiteWith :
    (honeycombTorusGraph m).IsBipartiteWith
      (honeycombSublatticeA m) (honeycombSublatticeB m) where
  disjoint := by
    rw [Set.disjoint_left]
    rintro v hvA hvB
    rw [honeycombSublatticeA, Set.mem_setOf_eq] at hvA
    rw [honeycombSublatticeB, Set.mem_setOf_eq] at hvB
    rw [hvA] at hvB
    exact Bool.noConfusion hvB
  mem_of_adj := by
    rintro v w (⟨hv, hw, -⟩ | ⟨hv, hw, -⟩)
    · exact Or.inl ⟨hv, hw⟩
    · exact Or.inr ⟨hv, hw⟩

/-- The honeycomb torus is **bipartite** (`Colorable 2`). -/
theorem honeycombTorusGraph_isBipartite :
    (honeycombTorusGraph m).IsBipartite :=
  (honeycombTorusGraph_isBipartiteWith m).isBipartite

/-! ### 3-regularity

Each `A`-site `((p, q), false)` is adjacent to exactly the three `B`-sites `((p, q), true)`,
`((p - 1, q), true)`, `((p, q - 1), true)`, and each `B`-site `((p, q), true)` to the three
`A`-sites `((p, q), false)`, `((p + 1, q), false)`, `((p, q + 1), false)`.  These three
neighbours are distinct precisely when `(1 : ZMod m) ≠ 0`, i.e. for `2 ≤ m`; on smaller tori
the honeycomb degenerates. -/

/-- The `A`-cell bond condition solved for the `B`-cell: the three cells joined to an
`A`-cell `(p, q)`. -/
private theorem honeycombBond_solved_A {p q : ZMod m} (a b : ZMod m) :
    honeycombBond (p, q) (a, b) ↔
      (a, b) = (p, q) ∨ (a, b) = (p - 1, q) ∨ (a, b) = (p, q - 1) := by
  simp only [honeycombBond]

/-- The `B`-cell bond condition solved for the `A`-cell: the three `A`-cells joined to a
`B`-cell `(p, q)` are `(p, q)`, `(p + 1, q)` and `(p, q + 1)`. -/
private theorem honeycombBond_solved_B {p q : ZMod m} (a b : ZMod m) :
    honeycombBond (a, b) (p, q) ↔
      (a, b) = (p, q) ∨ (a, b) = (p + 1, q) ∨ (a, b) = (p, q + 1) := by
  simp only [honeycombBond, Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inl ⟨by rw [h1]; ring, h2.symm⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, by rw [h2]; ring⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inl ⟨by rw [h1]; ring, h2.symm⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, by rw [h2]; ring⟩)

/-- The neighbour finset of an `A`-site `((p, q), false)`: the three adjacent `B`-sites. -/
private theorem honeycombTorusGraph_neighborFinset_A [NeZero m] (p q : ZMod m) :
    (honeycombTorusGraph m).neighborFinset ((p, q), false) =
      {((p, q), true), ((p - 1, q), true), ((p, q - 1), true)} := by
  ext w
  obtain ⟨⟨a, b⟩, t⟩ := w
  rw [SimpleGraph.mem_neighborFinset, honeycombTorusGraph_adj]
  cases t <;>
    simp [honeycombBond_solved_A, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]

/-- The neighbour finset of a `B`-site `((p, q), true)`: the three adjacent `A`-sites. -/
private theorem honeycombTorusGraph_neighborFinset_B [NeZero m] (p q : ZMod m) :
    (honeycombTorusGraph m).neighborFinset ((p, q), true) =
      {((p, q), false), ((p + 1, q), false), ((p, q + 1), false)} := by
  ext w
  obtain ⟨⟨a, b⟩, t⟩ := w
  rw [SimpleGraph.mem_neighborFinset, honeycombTorusGraph_adj]
  cases t <;>
    simp [honeycombBond_solved_B, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]

/-- The **honeycomb torus is `3`-regular** (Tasaki eq. (7.3.8), p. 211: coordination number
`3`, whence the uniform spin `S = 3/2`).  Requires `2 ≤ m` so that the three neighbours of
each site are distinct (on smaller tori they collide). -/
theorem honeycombTorusGraph_isRegularOfDegree [NeZero m] (hm : 2 ≤ m) :
    (honeycombTorusGraph m).IsRegularOfDegree 3 := by
  haveI : Fact (1 < m) := ⟨hm⟩
  have hne : (1 : ZMod m) ≠ 0 := one_ne_zero
  have hsub : ∀ x : ZMod m, x - 1 ≠ x := fun x h => hne (sub_eq_self.mp h)
  have hadd : ∀ x : ZMod m, x + 1 ≠ x :=
    fun x h => hne (add_left_cancel (h.trans (add_zero x).symm))
  intro v
  obtain ⟨⟨p, q⟩, t⟩ := v
  cases t
  · rw [SimpleGraph.degree, honeycombTorusGraph_neighborFinset_A]
    refine Finset.card_eq_three.mpr
      ⟨((p, q), true), ((p - 1, q), true), ((p, q - 1), true), ?_, ?_, ?_, rfl⟩
    · intro h; rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact hsub p h.1.1.symm
    · intro h; rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact hsub q h.1.2.symm
    · intro h; rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact hsub p h.1.1
  · rw [SimpleGraph.degree, honeycombTorusGraph_neighborFinset_B]
    refine Finset.card_eq_three.mpr
      ⟨((p, q), false), ((p + 1, q), false), ((p, q + 1), false), ?_, ?_, ?_, rfl⟩
    · intro h; rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact hadd p h.1.1.symm
    · intro h; rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact hadd q h.1.2.symm
    · intro h; rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact hadd p h.1.1

end LatticeSystem.Lattice
