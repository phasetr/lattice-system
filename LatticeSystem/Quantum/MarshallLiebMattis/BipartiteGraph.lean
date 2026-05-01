/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Bipartite graph from a sublattice indicator

Given a sublattice indicator `A : Λ → Bool`, this module defines
the **complete bipartite graph** on `Λ` whose edges are exactly
the pairs `(x, y)` with `A x ≠ A y`:

  `bipartiteGraphFromA A : SimpleGraph Λ` with `Adj x y ↔ A x ≠ A y`.

This is the natural graph for the MLM toy Hamiltonian (Tasaki §2.5
p. 40 eq. (2.5.10)): the bond graph where the toy `bipartiteCoupling`
is positive coincides with `bipartiteGraphFromA A`. Combined with
the assumption that both sublattices are non-empty, this graph is
preconnected, so the matrix-level MLM result (PR α-5o) applies to
the toy Hamiltonian on H_0.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 pp. 40–41.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*}

/-- The complete bipartite graph on `Λ` from a sublattice indicator
`A : Λ → Bool`: vertices `x, y` are adjacent iff `A x ≠ A y`.

This is the natural bond graph for the MLM toy Hamiltonian. -/
def bipartiteGraphFromA (A : Λ → Bool) : SimpleGraph Λ where
  Adj x y := A x ≠ A y
  symm := fun _ _ h heq => h heq.symm
  loopless := ⟨fun _ h => h rfl⟩

@[simp] theorem bipartiteGraphFromA_adj (A : Λ → Bool) (x y : Λ) :
    (bipartiteGraphFromA A).Adj x y ↔ A x ≠ A y := Iff.rfl

/-- Adjacency is symmetric: this is just the structure-symmetry. -/
theorem bipartiteGraphFromA_adj_symm (A : Λ → Bool) {x y : Λ}
    (h : (bipartiteGraphFromA A).Adj x y) :
    (bipartiteGraphFromA A).Adj y x :=
  h.symm

/-- The sublattice graph is preconnected when both sublattices are
non-empty. Any two `x, y ∈ Λ` are joined by a walk of length ≤ 2:

* If `A x ≠ A y`: direct edge.
* If `A x = A y`: pick any `z` in the opposite sublattice (exists by
  non-emptiness of the other side); then `x ~ z ~ y` via two edges. -/
theorem bipartiteGraphFromA_preconnected
    (A : Λ → Bool) (hA_pos : ∃ x : Λ, A x = true) (hA_neg : ∃ y : Λ, A y = false) :
    (bipartiteGraphFromA A).Preconnected := by
  intro x y
  by_cases hxy : A x = A y
  · -- Same sublattice: pick a vertex in the opposite sublattice.
    by_cases hAx : A x = true
    · -- A x = true, so A y = true; pick z with A z = false.
      obtain ⟨z, hz⟩ := hA_neg
      have hxz : (bipartiteGraphFromA A).Adj x z := by
        simp [bipartiteGraphFromA, hAx, hz]
      have hyz : (bipartiteGraphFromA A).Adj y z := by
        simp [bipartiteGraphFromA, hxy ▸ hAx, hz]
      exact ⟨(SimpleGraph.Walk.nil.cons hxz).append
        ((SimpleGraph.Walk.nil.cons hyz).reverse)⟩
    · -- A x = false, so A y = false; pick z with A z = true.
      have hAxF : A x = false := by
        cases h : A x
        · rfl
        · exact absurd h hAx
      obtain ⟨z, hz⟩ := hA_pos
      have hxz : (bipartiteGraphFromA A).Adj x z := by
        simp [bipartiteGraphFromA, hAxF, hz]
      have hyz : (bipartiteGraphFromA A).Adj y z := by
        simp [bipartiteGraphFromA, hxy ▸ hAxF, hz]
      exact ⟨(SimpleGraph.Walk.nil.cons hxz).append
        ((SimpleGraph.Walk.nil.cons hyz).reverse)⟩
  · -- Different sublattices: direct edge.
    exact ⟨SimpleGraph.Walk.nil.cons hxy⟩

end LatticeSystem.Quantum
