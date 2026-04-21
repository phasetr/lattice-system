/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.SuccPred

/-!
# Graph-centric framework for many-body lattice systems

This is the foundational module that fixes the project's
**graph-centric** orientation: the underlying combinatorial datum of
every many-body system in this library is a graph `(Λ, E_Λ)`,
with `Λ` the vertex set (a `Type*`) and `E_Λ` either a
`SimpleGraph Λ` or, equivalently, the support of a coupling function
`J : Λ → Λ → ℂ`. Lattices such as the 1D chain, higher-dimensional
grids, or their infinite analogues `ℤ`, `ℤ^d` are treated as
**examples** of graphs (`pathGraph`, `cycleGraph`, products of
these, infinite analogues, …), not as a primary abstraction.

`Λ` is *not* assumed finite at this level; finiteness
(`[Fintype Λ]`) is added only locally where needed (e.g. for traces,
partition functions, finite sums of local terms). The framework is
intended to support both **finite-volume** work and the
**infinite-volume / thermodynamic limit** that is one of the
project's primary long-term goals.

This convention follows the standard mathematical-physics literature
on many-body systems on graphs — Lieb's theorem on bipartite
lattices, the Marshall–Lieb–Mattis theorem, Miyao 2021 (*An
algebraic approach to revealing magnetic structures of ground states
in many-electron systems*, §3, p. 9), and others.

The Heisenberg Hamiltonian
`H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` (defined in `Quantum/SpinDot.lean`)
is generic over the function `J : Λ → Λ → ℂ`. This module provides
the canonical bridge from a `SimpleGraph` to such a coupling
function.

This module provides:

* `couplingOf G J` — the canonical pairwise coupling associated with
  a `SimpleGraph G` and uniform edge weight `J : ℂ`. Returns `J` on
  edges of `G`, and `0` otherwise.
* Symmetry, diagonal, and real/Hermitian properties of `couplingOf`.
* Decidability for `pathGraph` adjacency.
* Identification of `pathGraph (N + 1)` / `cycleGraph (N + 2)`
  adjacency with the elementary `x.val + 1 = y.val ∨ ...` form
  used by `openChainCoupling` / `periodicChainCoupling`.
-/

namespace LatticeSystem.Lattice

open SimpleGraph

variable {Λ : Type*}

/-- The canonical pairwise coupling associated with a `SimpleGraph G`
on the lattice `Λ` and a uniform complex edge weight `J`: returns `J`
on adjacent pairs and `0` on non-adjacent pairs (including the
diagonal, since a `SimpleGraph` has no self-loops). -/
def couplingOf (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Λ → Λ → ℂ :=
  fun x y => if G.Adj x y then J else 0

/-- The coupling on the diagonal vanishes (no self-loops in a
`SimpleGraph`). -/
@[simp]
theorem couplingOf_self (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (J : ℂ) (x : Λ) : couplingOf G J x x = 0 := by
  unfold couplingOf
  rw [if_neg G.irrefl]

/-- The coupling is symmetric in `x, y` because `SimpleGraph.Adj` is
symmetric. -/
theorem couplingOf_symm (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (J : ℂ) (x y : Λ) :
    couplingOf G J x y = couplingOf G J y x := by
  unfold couplingOf
  by_cases h : G.Adj x y
  · rw [if_pos h, if_pos (G.symm h)]
  · rw [if_neg h, if_neg (fun h' => h (G.symm h'))]

/-- If the edge weight `J` is real (i.e. `star J = J`), every entry
of `couplingOf G J` is real. -/
theorem couplingOf_real (G : SimpleGraph Λ) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) (x y : Λ) :
    star (couplingOf G J x y) = couplingOf G J x y := by
  unfold couplingOf
  by_cases h : G.Adj x y
  · rw [if_pos h, hJ]
  · rw [if_neg h, star_zero]

/-! ## Standard one-dimensional chains as path / cycle graphs

The finite open / periodic chains used throughout the codebase are
particular instances of mathlib's `pathGraph` and `cycleGraph`. The
infinite chain `ℤ` and higher-dimensional infinite grids will be
added when infinite-volume work begins. -/

/-- Decidability for the path graph adjacency. mathlib provides only
the bare `pathGraph` definition; we add the `DecidableRel` instance
needed to use `pathGraph` with `couplingOf`. -/
instance pathGraph_decidableAdj (n : ℕ) :
    DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

/-- The open one-dimensional chain on `N + 1` sites is the path
graph `pathGraph (N + 1)`. We expose adjacency in the form used by
the rest of the codebase: `x.val + 1 = y.val ∨ y.val + 1 = x.val`. -/
theorem pathGraph_adj_iff (N : ℕ) (x y : Fin (N + 1)) :
    (pathGraph (N + 1)).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val :=
  pathGraph_adj

/-- The periodic one-dimensional chain on `N + 2` sites is the cycle
graph `cycleGraph (N + 2)`. mathlib's `cycleGraph_adj` gives the
equivalent form `u - v = 1 ∨ v - u = 1`; we re-package it in the
`x + 1 = y ∨ y + 1 = x` form used by the rest of the codebase. -/
theorem cycleGraph_adj_iff (N : ℕ) (x y : Fin (N + 2)) :
    (cycleGraph (N + 2)).Adj x y ↔ x + 1 = y ∨ y + 1 = x := by
  rw [cycleGraph_adj]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · exact Or.inr (sub_eq_iff_eq_add'.mp h).symm
    · exact Or.inl (sub_eq_iff_eq_add'.mp h).symm
  · rintro (h | h)
    · exact Or.inr (sub_eq_iff_eq_add'.mpr h.symm)
    · exact Or.inl (sub_eq_iff_eq_add'.mpr h.symm)

/-! ## Higher-dimensional lattices via the box product

mathlib's `SimpleGraph.boxProd` (notation `□`) takes
`G : SimpleGraph α` and `H : SimpleGraph β` and returns a graph on
`α × β` with adjacency
`(G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1`.
This realises the standard 2D / nD square (or cubic) lattices as
products of path / cycle graphs. -/

/-- Decidability for the box-product adjacency. -/
instance boxProd_decidableAdj
    {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff _ boxProd_adj.symm

/-! ## Infinite chain ℤ

The infinite one-dimensional chain on `ℤ` is the Hasse graph of the
integers (the cover relation `a ⋖ b` on `ℤ` is `b = a + 1`). This is
the natural infinite-volume analogue of `pathGraph (N + 1)`, and
makes the framework's support for **infinite graphs** explicit at
the graph level.

Many-body operators on infinite `Λ` require separate infrastructure
(the current `ManyBodyOp Λ = Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ`
representation needs `Fintype Λ`); that infrastructure will be added
when the infinite-volume / KMS-state work begins. -/

/-- The infinite one-dimensional chain on `ℤ` as a `SimpleGraph`,
the infinite analogue of `pathGraph (N + 1)`. -/
def integerChainGraph : SimpleGraph ℤ := hasse ℤ

/-- Adjacency in the integer chain: `a ~ b` iff `b = a + 1` or
`a = b + 1`. -/
theorem integerChainGraph_adj_iff (a b : ℤ) :
    integerChainGraph.Adj a b ↔ b = a + 1 ∨ a = b + 1 := by
  unfold integerChainGraph
  rw [hasse_adj]
  constructor
  · rintro (h | h)
    · exact Or.inl (Order.covBy_iff_add_one_eq.mp h).symm
    · exact Or.inr (Order.covBy_iff_add_one_eq.mp h).symm
  · rintro (h | h)
    · exact Or.inl (Order.covBy_iff_add_one_eq.mpr h.symm)
    · exact Or.inr (Order.covBy_iff_add_one_eq.mpr h.symm)

/-- Decidability for the integer chain adjacency. -/
instance integerChainGraph_decidableAdj :
    DecidableRel integerChainGraph.Adj := fun a b =>
  decidable_of_iff _ (integerChainGraph_adj_iff a b).symm

/-! ## Sum decomposition over pathGraph adjacency

Technical helpers for proving bridge theorems between chain-specific
operators (defined via `Σ_{i:Fin N} f (i.castSucc) (i.succ)`) and
graph-built ones (defined via `Σ_{x,y} (couplingOf (pathGraph _) _
x y) • f x y`). Each undirected edge of `pathGraph (N+1)` corresponds
to an `i : Fin N`, with two ordered adjacency pairs. -/

/-- Forward edges of `pathGraph (N+1)`: ordered pairs `(x, y)` with
`x.val + 1 = y.val` enumerate `Fin N` via `i ↦ (i.castSucc, i.succ)`. -/
lemma sum_pathGraph_forward {α : Type*} [AddCommMonoid α] (N : ℕ)
    (f : Fin (N + 1) → Fin (N + 1) → α) :
    ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      (if x.val + 1 = y.val then f x y else 0)
    = ∑ i : Fin N, f i.castSucc i.succ := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    ((i.castSucc, i.succ) : Fin (N + 1) × Fin (N + 1)))
  · intro i _; simp
  · intro i _ j _ hij
    exact Fin.castSucc_injective _ (Prod.ext_iff.mp hij).1
  · intro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hp
    refine ⟨⟨x.val, ?_⟩, Finset.mem_univ _, ?_⟩
    · have : x.val < N + 1 := x.isLt; omega
    · ext
      · rfl
      · simp [Fin.succ]; omega
  · intro i _; rfl

/-- Backward edges of `pathGraph (N+1)`: ordered pairs `(x, y)` with
`y.val + 1 = x.val` enumerate `Fin N` via `i ↦ (i.succ, i.castSucc)`. -/
lemma sum_pathGraph_backward {α : Type*} [AddCommMonoid α] (N : ℕ)
    (f : Fin (N + 1) → Fin (N + 1) → α) :
    ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      (if y.val + 1 = x.val then f x y else 0)
    = ∑ i : Fin N, f i.succ i.castSucc := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    ((i.succ, i.castSucc) : Fin (N + 1) × Fin (N + 1)))
  · intro i _; simp
  · intro i _ j _ hij
    exact Fin.succ_injective _ (Prod.ext_iff.mp hij).1
  · intro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hp
    refine ⟨⟨y.val, ?_⟩, Finset.mem_univ _, ?_⟩
    · have : y.val < N + 1 := y.isLt; omega
    · ext
      · simp [Fin.succ]; omega
      · rfl
  · intro i _; rfl

/-- **Sum over `pathGraph (N+1)` adjacency decomposes into forward
+ backward edge sums**: the double sum over adjacent ordered pairs
equals `Σ_i (f cs s + f s cs)` where `i : Fin N` ranges over the
unordered edges. -/
lemma sum_pathGraph_adj {α : Type*} [AddCommMonoid α] (N : ℕ)
    (f : Fin (N + 1) → Fin (N + 1) → α) :
    ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      (if (SimpleGraph.pathGraph (N + 1)).Adj x y then f x y else 0)
    = ∑ i : Fin N, (f i.castSucc i.succ + f i.succ i.castSucc) := by
  have key : ∀ x y : Fin (N + 1),
      (if (SimpleGraph.pathGraph (N + 1)).Adj x y then f x y else 0)
      = (if x.val + 1 = y.val then f x y else 0)
        + (if y.val + 1 = x.val then f x y else 0) := by
    intro x y
    by_cases h : (SimpleGraph.pathGraph (N + 1)).Adj x y
    · rw [if_pos h, SimpleGraph.pathGraph_adj] at *
      rcases h with h | h
      · rw [if_pos h, if_neg (by omega : ¬ y.val + 1 = x.val), add_zero]
      · rw [if_neg (by omega : ¬ x.val + 1 = y.val), if_pos h, zero_add]
    · rw [SimpleGraph.pathGraph_adj] at h
      rw [if_neg (show ¬ (SimpleGraph.pathGraph (N + 1)).Adj x y by
        rw [SimpleGraph.pathGraph_adj]; exact h)]
      rw [if_neg (by tauto : ¬ x.val + 1 = y.val),
          if_neg (by tauto : ¬ y.val + 1 = x.val), add_zero]
  simp_rw [key, Finset.sum_add_distrib]
  rw [sum_pathGraph_forward, sum_pathGraph_backward,
    ← Finset.sum_add_distrib]

/-- The 2D infinite square lattice on `ℤ × ℤ` as a `SimpleGraph`,
the box product of two integer chains. Adjacency: nearest neighbours
in one coordinate, equal in the other. Infinite-volume analogue of
the finite `squareLatticeCoupling` (PR #141). -/
def integerSquareLatticeGraph : SimpleGraph (ℤ × ℤ) :=
  integerChainGraph □ integerChainGraph

/-- Adjacency in the 2D infinite square lattice: a horizontal step
or a vertical step. -/
theorem integerSquareLatticeGraph_adj_iff (x y : ℤ × ℤ) :
    integerSquareLatticeGraph.Adj x y ↔
      (integerChainGraph.Adj x.1 y.1 ∧ x.2 = y.2) ∨
        (integerChainGraph.Adj x.2 y.2 ∧ x.1 = y.1) :=
  boxProd_adj

end LatticeSystem.Lattice
