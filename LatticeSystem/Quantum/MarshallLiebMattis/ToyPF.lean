import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian
import LatticeSystem.Quantum.MarshallLiebMattis.BipartiteGraph
import LatticeSystem.Quantum.MarshallLiebMattis.H0PFApplication

/-!
# MLM matrix-level Tasaki (2.5.4) for the toy Hamiltonian

Specialises the matrix-level MLM result (PR α-5o) to the toy
Hamiltonian (PR α-6a) via the bipartite graph from the sublattice
indicator (PR α-6b):

For both sublattices non-empty and a shift constant `c` strictly
larger than every diagonal entry of `M_toy = dressedHeisenbergMatrixH0
A (bipartiteCoupling A)`, the shifted toy matrix
`B_toy = c · I − M_toy` admits a **unique-up-to-positive-scalar
strictly positive eigenvector** for some real eigenvalue.

This is the toy-Hamiltonian instance of the matrix-level MLM
(Tasaki §2.5 (2.5.4)). Subsequent PRs use this together with the
Casimir identity to derive `S_tot = 0` for the AFM Heisenberg
ground state in `H_0`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 pp. 40–41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The bipartite coupling and bipartite graph are mutually
consistent: bipartiteGraphFromA-edges coincide with positive
bipartiteCoupling. -/
private theorem bipartite_pos_on_graph (A : Λ → Bool) :
    ∀ {x y : Λ}, (bipartiteGraphFromA A).Adj x y →
      0 < (bipartiteCoupling A x y).re := by
  intro x y hadj
  rw [bipartiteGraphFromA_adj] at hadj
  exact bipartiteCoupling_pos_of_diff_sublattice A hadj

set_option linter.unusedSectionVars false in
/-- The bipartite graph is bipartite-respecting: each edge crosses
the sublattice partition. -/
private theorem bipartite_graph_bipartite (A : Λ → Bool) :
    ∀ {x y : Λ}, (bipartiteGraphFromA A).Adj x y → A x ≠ A y := by
  intro x y hadj
  rwa [bipartiteGraphFromA_adj] at hadj

/-- **Matrix-level Tasaki (2.5.4) for the toy Hamiltonian**.

For both sublattices non-empty and `c` strictly greater than every
diagonal entry of the dressed toy matrix, the shifted toy matrix
`B_toy = c · I − M_toy` has a unique-up-to-positive-scalar strictly
positive eigenvector. -/
theorem dressedHeisenbergShifted_toy_exists_pos_eigenvec_max
    [Nonempty (H₀Index Λ)]
    (A : Λ → Bool) (hA_pos : ∃ x : Λ, A x = true)
    (hA_neg : ∃ y : Λ, A y = false)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ,
      dressedHeisenbergMatrixH0 A (bipartiteCoupling A) σ σ < c) :
    ∃ (μ : ℝ) (v : H₀Index Λ → ℝ),
      (dressedHeisenbergShifted A (bipartiteCoupling A) c).mulVec v = μ • v ∧
      v ≠ 0 ∧ ∀ σ, 0 < v σ :=
  dressedHeisenbergShifted_exists_pos_eigenvec_max
    (bipartiteGraphFromA_preconnected A hA_pos hA_neg) A
    (bipartite_graph_bipartite A) (bipartiteCoupling_im A)
    (bipartiteCoupling_symm A) (bipartiteCoupling_nonneg A)
    (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
    (bipartite_pos_on_graph A) c hc

/-- **Uniqueness up to positive scalar** for the toy Hamiltonian's
PF eigenvector. -/
theorem dressedHeisenbergShifted_toy_pos_eigenvec_unique
    [Nonempty (H₀Index Λ)]
    (A : Λ → Bool) (hA_pos : ∃ x : Λ, A x = true)
    (hA_neg : ∃ y : Λ, A y = false)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ,
      dressedHeisenbergMatrixH0 A (bipartiteCoupling A) σ σ < c)
    {μ : ℝ} {v w : H₀Index Λ → ℝ}
    (hv : (dressedHeisenbergShifted A (bipartiteCoupling A) c).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergShifted A (bipartiteCoupling A) c).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v :=
  dressedHeisenbergShifted_pos_eigenvec_unique
    (bipartiteGraphFromA_preconnected A hA_pos hA_neg) A
    (bipartite_graph_bipartite A) (bipartiteCoupling_im A)
    (bipartiteCoupling_symm A) (bipartiteCoupling_nonneg A)
    (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
    (bipartite_pos_on_graph A) c hc hv hv_pos hw hw_pos

end LatticeSystem.Quantum
