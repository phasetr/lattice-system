import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Maps
import LatticeSystem.Lattice.Graph
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Ring.Int.Parity

/-!
# The infinite hypercubic lattice `ℤᵈ` and its finite-volume exhaustion

This module fixes the **graph-centric** datum underlying the project's central
long-term goal — the thermodynamic (infinite-volume) limit on the
`d`-dimensional hypercubic lattice `ℤᵈ`.  Finite-volume systems are the starting
point; the infinite system is obtained as the limit along an increasing sequence
of finite boxes `Λ_n ⊆ Λ_{n+1} ⊆ ⋯` that exhaust `ℤᵈ`.

It provides, with no quantum / C*-algebra dependencies:

* `hypercubicLatticeGraph d : SimpleGraph (Fin d → ℤ)` — the infinite hypercubic
  lattice as a `SimpleGraph`, with two sites adjacent iff they differ in exactly
  one coordinate by `±1` (the nearest-neighbor bond set `B∞`, cf. Tasaki
  eq. (4.3.1));
* `hypercubicBox d n : Finset (Fin d → ℤ)` — the centered finite box
  `Λ_n = {x ∈ ℤᵈ : −n < xᵢ ≤ n}` of even side length `2n` (Tasaki eq. (3.1.2));
* the **monotone exhaustion** of `ℤᵈ` by the boxes: `Λ_n ⊆ Λ_{n+1}`
  (`hypercubicBox_subset_succ`, `hypercubicBox_monotone`) and
  `⋃ₙ Λ_n = ℤᵈ` (`iUnion_hypercubicBox`, `exists_mem_hypercubicBox`).

The box `hypercubicBox d n` is definitionally the same `Fintype.piFinset` as
`LatticeSystem.Quantum.InfiniteSpinSystem.latticeBox d n`; this model-agnostic
copy lives in `Lattice/` so the increasing-region API is available without the
quantum layer.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §3.1 (eq. (3.1.2)) and §4.3 (eq. (4.3.1)).
-/

namespace LatticeSystem.Lattice

open Finset

variable (d : ℕ)

/-- The **infinite hypercubic lattice** `ℤᵈ` as a `SimpleGraph (Fin d → ℤ)`: two
sites `x, y` are adjacent iff they differ in exactly one coordinate by `±1`,
i.e. there is a coordinate `i` with `|xᵢ − yᵢ| = 1` and `xⱼ = yⱼ` for every
`j ≠ i`.  This is the nearest-neighbor bond set `B∞` of Tasaki eq. (4.3.1). -/
def hypercubicLatticeGraph : SimpleGraph (Fin d → ℤ) where
  Adj x y := ∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j
  symm := by
    rintro x y ⟨i, hi, hj⟩
    exact ⟨i, by rw [abs_sub_comm]; exact hi, fun j hjne => (hj j hjne).symm⟩
  loopless := ⟨by rintro x ⟨i, hi, -⟩; simp at hi⟩

variable {d}

/-- Adjacency in `hypercubicLatticeGraph d` unfolds to the nearest-neighbor bond
condition: `x` and `y` differ in exactly one coordinate by `±1`. -/
theorem hypercubicLatticeGraph_adj {x y : Fin d → ℤ} :
    (hypercubicLatticeGraph d).Adj x y ↔
      ∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j :=
  Iff.rfl

instance : DecidableRel (hypercubicLatticeGraph d).Adj := fun x y =>
  decidable_of_iff (∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j)
    hypercubicLatticeGraph_adj.symm

variable (d)

/-- The centered finite **hypercubic box** `Λ_n = {x ∈ ℤᵈ : −n < xᵢ ≤ n}` of even
side length `2n` and volume `(2n)ᵈ` (Tasaki eq. (3.1.2)), as a `Finset`.  This is
definitionally equal to `Quantum.InfiniteSpinSystem.latticeBox d n`. -/
noncomputable def hypercubicBox (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ioc (-(n : ℤ)) (n : ℤ)

variable {d}

/-- Membership in the hypercubic box: `x ∈ Λ_n` iff every coordinate satisfies
`−n < xᵢ ≤ n`. -/
@[simp]
theorem mem_hypercubicBox {n : ℕ} {x : Fin d → ℤ} :
    x ∈ hypercubicBox d n ↔ ∀ i, -(n : ℤ) < x i ∧ x i ≤ (n : ℤ) := by
  simp [hypercubicBox, Fintype.mem_piFinset, Finset.mem_Ioc]

/-- The boxes are **nested**: `Λ_n ⊆ Λ_{n+1}`. -/
theorem hypercubicBox_subset_succ (n : ℕ) :
    hypercubicBox d n ⊆ hypercubicBox d (n + 1) := by
  apply Fintype.piFinset_subset
  intro _
  apply Finset.Ioc_subset_Ioc
  · push_cast; omega
  · push_cast; omega

/-- The box family is **monotone** in the side index `n` (as a function to
`Finset`s under `⊆`). -/
theorem hypercubicBox_monotone : Monotone (hypercubicBox d) := by
  apply monotone_nat_of_le_succ
  intro n
  exact hypercubicBox_subset_succ n

/-- Every site of `ℤᵈ` lies in some box: the boxes **exhaust** `ℤᵈ`.  Concretely
`x ∈ Λ_n` for any `n` exceeding every `|xᵢ|`. -/
theorem exists_mem_hypercubicBox (x : Fin d → ℤ) :
    ∃ n : ℕ, x ∈ hypercubicBox d n := by
  refine ⟨(Finset.univ.sup fun i => (x i).natAbs) + 1, ?_⟩
  rw [mem_hypercubicBox]
  intro i
  have hle : (x i).natAbs ≤ Finset.univ.sup fun i => (x i).natAbs :=
    Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  constructor <;> push_cast <;> omega

/-- The boxes **exhaust** `ℤᵈ`: `⋃ₙ Λ_n = ℤᵈ`. -/
theorem iUnion_hypercubicBox :
    ⋃ n : ℕ, (hypercubicBox d n : Set (Fin d → ℤ)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨n, hn⟩ := exists_mem_hypercubicBox x
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

/-- The **volume** of the finite box is `(2n)ᵈ`: `|Λ_n| = (2n)ᵈ` (the box has
side length `2n` in each of the `d` directions, Tasaki §4.3).  This is the volume
normalization `Lᵈ = (2n)ᵈ` of the bulk-density / energy-density limits
(eqs. (4.3.4), (4.3.6)). -/
theorem hypercubicBox_card (d n : ℕ) : (hypercubicBox d n).card = (2 * n) ^ d := by
  rw [hypercubicBox, Fintype.card_piFinset_const, Int.card_Ioc]
  congr 1
  omega

/-! ### Bipartite structure: the even/odd parity sublattices

The hypercubic lattice `ℤᵈ` is bipartite: a nearest-neighbor bond flips the
parity of the coordinate sum `Σᵢ xᵢ`, so the **even** sublattice
`ℤᵈ_even = {x : Σᵢ xᵢ even}` (the A-sublattice, Tasaki eq. (4.3.2)) and its
complement (the B-sublattice) are the two color classes.  This is the
combinatorial structure underlying antiferromagnetic / Néel order. -/

/-- A nearest-neighbor bond flips the parity of the coordinate sum: if `x` and
`y` are adjacent then `Σᵢ xᵢ` and `Σᵢ yᵢ` have **opposite** parity. -/
theorem hypercubicLatticeGraph_adj_parity_ne {x y : Fin d → ℤ}
    (h : (hypercubicLatticeGraph d).Adj x y) :
    ¬ (Even (∑ i, x i) ↔ Even (∑ i, y i)) := by
  obtain ⟨i, hi, hj⟩ := h
  have hsum : (∑ k, x k) - ∑ k, y k = x i - y i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · intro k _ hki; rw [hj k hki, sub_self]
    · intro hni; exact absurd (Finset.mem_univ i) hni
  have hb : (0 : ℤ) ≤ 1 := zero_le_one
  have hodd : ¬ Even (x i - y i) := by
    rcases (abs_eq hb).mp hi with h1 | h1 <;> rw [h1, Int.even_iff] <;> omega
  rw [← hsum] at hodd
  rwa [Int.even_sub] at hodd

/-- The **even sublattice** `ℤᵈ_even = {x : Σᵢ xᵢ even}` (the A-sublattice, Tasaki
eq. (4.3.2)), the first color class of the bipartition. -/
def hypercubicEvenSublattice (d : ℕ) : Set (Fin d → ℤ) :=
  {x | Even (∑ i, x i)}

/-- The **odd sublattice** `ℤᵈ_odd = {x : Σᵢ xᵢ odd}` (the B-sublattice), the
second color class of the bipartition. -/
def hypercubicOddSublattice (d : ℕ) : Set (Fin d → ℤ) :=
  {x | ¬ Even (∑ i, x i)}

variable (d) in
/-- The hypercubic lattice `ℤᵈ` is **bipartite with the even/odd sublattices** as
the two parts: every nearest-neighbor bond joins an even site to an odd site
(Tasaki §4.3, eq. (4.3.2)). -/
theorem hypercubicLatticeGraph_isBipartiteWith :
    (hypercubicLatticeGraph d).IsBipartiteWith
      (hypercubicEvenSublattice d) (hypercubicOddSublattice d) where
  disjoint := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx' hx
  mem_of_adj := by
    intro v w h
    have hp := hypercubicLatticeGraph_adj_parity_ne h
    by_cases hv : Even (∑ i, v i)
    · exact Or.inl ⟨hv, fun hw => hp (iff_of_true hv hw)⟩
    · exact Or.inr ⟨hv, by by_contra hw; exact hp (iff_of_false hv hw)⟩

/-- The parity 2-coloring of `ℤᵈ`: a site is colored by the parity of its
coordinate sum (`0` for even, `1` for odd). -/
def hypercubicParityColoring (d : ℕ) :
    (hypercubicLatticeGraph d).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun x => if Even (∑ i, x i) then 0 else 1)
    (fun {x y} h => by
      have hp := hypercubicLatticeGraph_adj_parity_ne h
      by_cases hx : Even (∑ i, x i) <;> by_cases hy : Even (∑ i, y i) <;>
        simp_all)

variable (d) in
/-- The hypercubic lattice `ℤᵈ` is **bipartite** (`Colorable 2`). -/
theorem hypercubicLatticeGraph_isBipartite :
    (hypercubicLatticeGraph d).IsBipartite :=
  ⟨hypercubicParityColoring d⟩

/-! ### The induced finite-volume subgraph on a box

The finite box `Λ_n` carries the **induced** subgraph of the hypercubic lattice:
a finite graph on which finite-volume Hamiltonians live.  This is the graph-centric
finite-volume substrate `Λ_n ↪ ℤᵈ` of the thermodynamic limit. -/

/-- The vertex type of the finite hypercubic box `Λ_n` (a subtype of `ℤᵈ`); a
`Fintype` since the box is a `Finset`. -/
abbrev hypercubicBoxVertex (d n : ℕ) : Type :=
  (hypercubicBox d n : Set (Fin d → ℤ))

/-- The **finite-volume graph** on the box `Λ_n`: the subgraph of the infinite
hypercubic lattice `ℤᵈ` induced on the vertices of `Λ_n`. -/
abbrev hypercubicBoxGraph (d n : ℕ) : SimpleGraph (hypercubicBoxVertex d n) :=
  (hypercubicLatticeGraph d).induce (hypercubicBox d n : Set (Fin d → ℤ))

/-- Adjacency in the finite-volume box graph is the parent nearest-neighbor bond
condition on the underlying sites. -/
theorem hypercubicBoxGraph_adj {d n : ℕ} {x y : hypercubicBoxVertex d n} :
    (hypercubicBoxGraph d n).Adj x y ↔
      ∃ i : Fin d, |(x : Fin d → ℤ) i - (y : Fin d → ℤ) i| = 1 ∧
        ∀ j, j ≠ i → (x : Fin d → ℤ) j = (y : Fin d → ℤ) j :=
  hypercubicLatticeGraph_adj

/-- The **uniform nearest-neighbor coupling** on the finite box `Λ_n` with edge
weight `J`: `J` on adjacent sites of the induced box graph, `0` otherwise.  This
is the graph-centric finite-volume coupling for many-body Hamiltonians. -/
noncomputable def hypercubicBoxCoupling (d n : ℕ) (J : ℂ) :
    hypercubicBoxVertex d n → hypercubicBoxVertex d n → ℂ :=
  couplingOf (hypercubicBoxGraph d n) J

/-- The parity 2-coloring of the finite-volume box graph: the parent lattice
parity coloring restricted along the inclusion `Λ_n ↪ ℤᵈ`. -/
def hypercubicBoxParityColoring (d n : ℕ) :
    (hypercubicBoxGraph d n).Coloring (Fin 2) :=
  (hypercubicParityColoring d).comp
    (SimpleGraph.Embedding.induce (hypercubicBox d n : Set (Fin d → ℤ))).toHom

variable (d n : ℕ) in
/-- The finite-volume box graph is **bipartite** (inherited from `ℤᵈ`). -/
theorem hypercubicBoxGraph_isBipartite :
    (hypercubicBoxGraph d n).IsBipartite :=
  ⟨hypercubicBoxParityColoring d n⟩

end LatticeSystem.Lattice
