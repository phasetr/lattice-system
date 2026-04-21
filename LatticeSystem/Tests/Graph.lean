/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Lattice.Graph
import LatticeSystem.Quantum.HeisenbergChain

/-!
# Test coverage for `LatticeSystem.Lattice.Graph`

Backfill regression tests for the graph framework introduced in
PR #138 (and extended through PR #150). Each block is either an
`example`-block proof or a `decide`-driven property test over a
small finite graph instance.
-/

namespace LatticeSystem.Tests.Graph

open LatticeSystem.Lattice LatticeSystem.Quantum SimpleGraph

/-! ## `couplingOf` algebraic properties -/

/-- Diagonal vanishing on `pathGraph 3`. -/
example (J : ℂ) : ∀ x : Fin 3, couplingOf (pathGraph 3) J x x = 0 := by
  intro x
  exact couplingOf_self _ J x

/-- Symmetry on `pathGraph 3` (universally quantified). -/
example (J : ℂ) : ∀ x y : Fin 3,
    couplingOf (pathGraph 3) J x y = couplingOf (pathGraph 3) J y x := by
  intro x y
  exact couplingOf_symm _ J x y

/-- Diagonal vanishing on `cycleGraph 4`. -/
example (J : ℂ) : ∀ x : Fin 4, couplingOf (cycleGraph 4) J x x = 0 := by
  intro x
  exact couplingOf_self _ J x

/-- Symmetry on `cycleGraph 4`. -/
example (J : ℂ) : ∀ x y : Fin 4,
    couplingOf (cycleGraph 4) J x y = couplingOf (cycleGraph 4) J y x := by
  intro x y
  exact couplingOf_symm _ J x y

/-- For real `J`, every entry of `couplingOf G J` is real. -/
example {J : ℂ} (hJ : star J = J) (x y : Fin 3) :
    star (couplingOf (pathGraph 3) J x y) = couplingOf (pathGraph 3) J x y :=
  couplingOf_real _ hJ x y

/-! ## `pathGraph` adjacency: `decide`-driven property tests -/

/-- `pathGraph 4`: every adjacency satisfies the symmetric form
`x.val + 1 = y.val ∨ y.val + 1 = x.val`. -/
example : ∀ x y : Fin 4,
    (pathGraph 4).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  decide

/-- `pathGraph 4` is irreflexive (universal). -/
example : ∀ x : Fin 4, ¬ (pathGraph 4).Adj x x := by decide

/-- `pathGraph 4` has exactly 3 edges (one per consecutive pair),
6 ordered adjacencies. -/
example :
    (Finset.univ.filter
      (fun p : Fin 4 × Fin 4 => (pathGraph 4).Adj p.1 p.2)).card = 6 := by
  decide

/-! ## `cycleGraph` adjacency: `decide`-driven property tests -/

/-- `cycleGraph 4`: each vertex has exactly two neighbours. -/
example : ∀ x : Fin 4,
    (Finset.univ.filter (fun y : Fin 4 => (cycleGraph 4).Adj x y)).card = 2 := by
  decide

/-- `cycleGraph 5` is irreflexive. -/
example : ∀ x : Fin 5, ¬ (cycleGraph 5).Adj x x := by decide

/-- `cycleGraph 5` has 10 ordered adjacencies (5 unordered edges). -/
example :
    (Finset.univ.filter
      (fun p : Fin 5 × Fin 5 => (cycleGraph 5).Adj p.1 p.2)).card = 10 := by
  decide

/-! ## boxProd adjacency on small product graphs -/

/-- `pathGraph 2 □ pathGraph 2` (2×2 lattice = 4-cycle): each vertex has
exactly 2 neighbours. -/
example : ∀ x : Fin 2 × Fin 2,
    (Finset.univ.filter
      (fun y : Fin 2 × Fin 2 => (pathGraph 2 □ pathGraph 2).Adj x y)).card = 2 := by
  decide

/-! ## Bridges to chain couplings -/

/-- The 2-site open chain coupling matches `couplingOf (pathGraph 2) (-J)`. -/
example (J : ℝ) :
    openChainCoupling 1 J = couplingOf (pathGraph 2) (-(J : ℂ)) :=
  openChainCoupling_eq_couplingOf 1 J

/-- The 3-site open chain coupling matches `couplingOf (pathGraph 3) (-J)`. -/
example (J : ℝ) :
    openChainCoupling 2 J = couplingOf (pathGraph 3) (-(J : ℂ)) :=
  openChainCoupling_eq_couplingOf 2 J

/-- The 3-site periodic chain coupling matches
`couplingOf (cycleGraph 3) (-J)`. -/
example (J : ℝ) :
    periodicChainCoupling 1 J = couplingOf (cycleGraph 3) (-(J : ℂ)) :=
  periodicChainCoupling_eq_couplingOf 1 J

/-- The 4-site periodic chain coupling matches
`couplingOf (cycleGraph 4) (-J)`. -/
example (J : ℝ) :
    periodicChainCoupling 2 J = couplingOf (cycleGraph 4) (-(J : ℂ)) :=
  periodicChainCoupling_eq_couplingOf 2 J

/-! ## integerChainGraph (infinite) -/

/-- The integer-chain adjacency on a fixed pair: `0 ~ 1`. -/
example : integerChainGraph.Adj 0 1 := by
  rw [integerChainGraph_adj_iff]
  left; ring

/-- `0 ≁ 0` (irreflexivity). -/
example : ¬ integerChainGraph.Adj 0 0 := integerChainGraph.irrefl

/-- `0 ≁ 2` (no second-neighbour edge). -/
example : ¬ integerChainGraph.Adj 0 2 := by
  rw [integerChainGraph_adj_iff]
  rintro (h | h) <;> omega

/-- Adjacency for negative integers: `(-3) ~ (-2)`. -/
example : integerChainGraph.Adj (-3) (-2) := by
  rw [integerChainGraph_adj_iff]; left; ring

/-- Symmetry: `(-2) ~ (-3)`. -/
example : integerChainGraph.Adj (-2) (-3) := by
  rw [integerChainGraph_adj_iff]; right; ring

/-- `5 ≁ 7` (distance 2, not adjacent). -/
example : ¬ integerChainGraph.Adj 5 7 := by
  rw [integerChainGraph_adj_iff]
  rintro (h | h) <;> omega

/-- `(-1) ≁ 1` (distance 2, not adjacent). -/
example : ¬ integerChainGraph.Adj (-1) 1 := by
  rw [integerChainGraph_adj_iff]
  rintro (h | h) <;> omega

/-- Irreflexivity for arbitrary `n : ℤ`. -/
example (n : ℤ) : ¬ integerChainGraph.Adj n n := integerChainGraph.irrefl

/-! ## integerSquareLatticeGraph (2D infinite ℤ × ℤ) -/

/-- Horizontal step: `(0, 0) ~ (1, 0)`. -/
example : integerSquareLatticeGraph.Adj (0, 0) (1, 0) := by
  rw [integerSquareLatticeGraph_adj_iff]
  left
  refine ⟨?_, rfl⟩
  rw [integerChainGraph_adj_iff]; left; ring

/-- Vertical step: `(0, 0) ~ (0, 1)`. -/
example : integerSquareLatticeGraph.Adj (0, 0) (0, 1) := by
  rw [integerSquareLatticeGraph_adj_iff]
  right
  refine ⟨?_, rfl⟩
  rw [integerChainGraph_adj_iff]; left; ring

/-- Diagonal non-step: `(0, 0) ≁ (1, 1)` (a single edge can change
only one coordinate). -/
example : ¬ integerSquareLatticeGraph.Adj (0, 0) (1, 1) := by
  rw [integerSquareLatticeGraph_adj_iff]
  rintro (⟨_, h⟩ | ⟨_, h⟩) <;> simp at h

/-- Irreflexivity for any `(a, b) : ℤ × ℤ`. -/
example (p : ℤ × ℤ) : ¬ integerSquareLatticeGraph.Adj p p :=
  integerSquareLatticeGraph.irrefl

end LatticeSystem.Tests.Graph
