import LatticeSystem.Quantum.SpinS.GraphLocalStarBlockCore
import LatticeSystem.Quantum.SpinS.SingleClusterTransport

/-!
# Fixed-outside blocks of graph-local star Hamiltonians

This file adds the block-level bridge needed for Tasaki §2.5 Problem 2.5.b:
after fixing the spins outside a center `x` and its graph neighbors, the
same-Hilbert-space graph-local star Hamiltonian centered at `x` has the same
matrix entries as the finite option-star Hamiltonian on
`Option (G.neighborFinset x)`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Block identity for graph-local star Hamiltonians -/

/-- If two full configurations differ outside the center and its graph
neighbors, the graph-local star Hamiltonian centered at `x` has zero matrix
entry between them. -/
theorem graphLocalClusterHamiltonianS_apply_eq_zero_of_outside_diff
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k : Λ, k ≠ x → k ∉ G.neighborFinset x → σ' k = σ k) :
    (graphLocalClusterHamiltonianS G x N : ManyBodyOpS Λ N) σ' σ = 0 := by
  unfold graphLocalClusterHamiltonianS
  rw [Matrix.sum_apply]
  change (∑ y ∈ G.neighborFinset x,
      (spinSDot x y N : ManyBodyOpS Λ N) σ' σ) = 0
  rw [Finset.sum_eq_zero]
  intro y hy
  have hyadj : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
  have hxy : x ≠ y := G.ne_of_adj hyadj
  apply spinSDot_apply_eq_zero_of_off_two_site_diff hxy N
  intro hagree
  apply h
  intro k hkx hknot
  exact hagree k hkx (by
    intro hky
    apply hknot
    rw [hky]
    exact hy)

/-- The fixed-outside block of the same-Hilbert-space graph-local star
Hamiltonian is the finite option-star Hamiltonian on the center and neighbor
set. -/
theorem graphLocalClusterHamiltonianS_block_eq_optionClusterHamiltonianS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (η : Λ → Fin (N + 1)) :
    (graphLocalClusterHamiltonianS G x N).submatrix
        (graphLocalStarConfig G x N η) (graphLocalStarConfig G x N η) =
      optionClusterHamiltonianS (G.neighborFinset x) N := by
  ext τ' τ
  unfold graphLocalClusterHamiltonianS optionClusterHamiltonianS
  rw [Matrix.submatrix_apply]
  rw [Matrix.sum_apply, Matrix.sum_apply]
  change (∑ y ∈ G.neighborFinset x,
      (spinSDot x y N : ManyBodyOpS Λ N)
        (graphLocalStarConfig G x N η τ')
        (graphLocalStarConfig G x N η τ)) =
    ∑ y : G.neighborFinset x,
      (spinSDot none (some y) N :
        ManyBodyOpS (Option (G.neighborFinset x)) N) τ' τ
  rw [← Finset.sum_attach (s := G.neighborFinset x)
    (f := fun y =>
      (spinSDot x y N : ManyBodyOpS Λ N)
        (graphLocalStarConfig G x N η τ')
        (graphLocalStarConfig G x N η τ))]
  refine Finset.sum_congr rfl ?_
  intro y _
  exact spinSDot_graphLocalStarConfig_eq_option G x N η τ' τ y

end LatticeSystem.Quantum
