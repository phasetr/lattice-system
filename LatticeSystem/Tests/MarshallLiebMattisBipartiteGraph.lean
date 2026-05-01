/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.BipartiteGraph

/-!
# Test coverage for the bipartite graph from a sublattice indicator
-/

namespace LatticeSystem.Tests.MarshallLiebMattisBipartiteGraph

open LatticeSystem.Quantum

/-- Adjacency in the bipartite graph from sublattice indicator `A`. -/
example (A : Fin 2 → Bool) (x y : Fin 2) :
    (bipartiteGraphFromA A).Adj x y ↔ A x ≠ A y :=
  bipartiteGraphFromA_adj A x y

/-- Adjacency is symmetric. -/
example (A : Fin 2 → Bool) {x y : Fin 2}
    (h : (bipartiteGraphFromA A).Adj x y) :
    (bipartiteGraphFromA A).Adj y x :=
  bipartiteGraphFromA_adj_symm A h

/-- Preconnectedness when both sublattices non-empty. -/
example (A : Fin 2 → Bool) (hA_pos : ∃ x, A x = true)
    (hA_neg : ∃ y, A y = false) :
    (bipartiteGraphFromA A).Preconnected :=
  bipartiteGraphFromA_preconnected A hA_pos hA_neg

end LatticeSystem.Tests.MarshallLiebMattisBipartiteGraph
