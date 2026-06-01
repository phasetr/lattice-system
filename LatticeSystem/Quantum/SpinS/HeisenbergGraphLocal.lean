import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Graph-local decomposition of spin-`S` Heisenberg Hamiltonians

This file packages the local star terms used in Tasaki §2.5 Problem 2.5.b.
The repository's graph Hamiltonian uses an ordered-pair sum, so the unit-coupling
graph Hamiltonian is the sum of all vertex-star terms.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Local graph-star Hamiltonians -/

/-- The graph-local star Hamiltonian centred at `x`:
`h_x = ∑_{y ∈ N_G(x)} Ŝ_x · Ŝ_y`.

This operator lives on the full many-body Hilbert space over `Λ`; it is the
same-Hilbert-space local term that will later be compared with the abstract
single-cluster Hamiltonian on `Fin (G.degree x + 1)`. -/
noncomputable def graphLocalClusterHamiltonianS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ) :
    ManyBodyOpS Λ N :=
  ∑ y ∈ G.neighborFinset x, spinSDot x y N

/-- Each graph-local star Hamiltonian is Hermitian. -/
theorem graphLocalClusterHamiltonianS_isHermitian
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ) :
    (graphLocalClusterHamiltonianS G x N).IsHermitian := by
  unfold graphLocalClusterHamiltonianS
  classical
  induction G.neighborFinset x using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert y s hys ih =>
    rw [Finset.sum_insert hys]
    exact Matrix.IsHermitian.add (spinSDot_isHermitian x y N) ih

/-- The unit-coupling graph Hamiltonian is the sum of all graph-local star
Hamiltonians.  This is the ordered-pair convention: each undirected edge appears
once from each endpoint. -/
theorem heisenbergHamiltonianOnGraphS_one_eq_sum_graphLocalClusterHamiltonianS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (N : ℕ) :
    heisenbergHamiltonianOnGraphS G (1 : ℂ) N =
      ∑ x : Λ, graphLocalClusterHamiltonianS G x N := by
  classical
  unfold heisenbergHamiltonianOnGraphS heisenbergHamiltonianS
    graphLocalClusterHamiltonianS LatticeSystem.Lattice.couplingOf
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [show (∑ y : Λ, (if G.Adj x y then (1 : ℂ) else 0) • spinSDot x y N) =
      ∑ y : Λ, if G.Adj x y then spinSDot x y N else 0 from by
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hxy : G.Adj x y
    · simp [hxy]
    · simp [hxy]]
  rw [show (∑ y : Λ, if G.Adj x y then spinSDot x y N else 0) =
      ∑ y ∈ (Finset.univ : Finset Λ).filter (G.Adj x), spinSDot x y N from by
    rw [← Finset.sum_filter]]
  rw [← SimpleGraph.neighborFinset_eq_filter]

/-- The half-coupling graph Hamiltonian is the sum of half-weighted
graph-local star Hamiltonians.  This is a coefficient-normalised form of the
ordered-pair decomposition. -/
theorem heisenbergHamiltonianOnGraphS_half_eq_sum_half_graphLocalClusterHamiltonianS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (N : ℕ) :
    heisenbergHamiltonianOnGraphS G ((1 : ℂ) / 2) N =
      ∑ x : Λ, ((1 : ℂ) / 2) • graphLocalClusterHamiltonianS G x N := by
  classical
  unfold heisenbergHamiltonianOnGraphS heisenbergHamiltonianS
    graphLocalClusterHamiltonianS LatticeSystem.Lattice.couplingOf
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [show (∑ y : Λ, (if G.Adj x y then (1 : ℂ) / 2 else 0) • spinSDot x y N) =
      ∑ y : Λ, if G.Adj x y then ((1 : ℂ) / 2) • spinSDot x y N else 0 from by
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hxy : G.Adj x y
    · simp [hxy]
    · simp [hxy]]
  rw [show (∑ y : Λ, if G.Adj x y then ((1 : ℂ) / 2) • spinSDot x y N else 0) =
      ((1 : ℂ) / 2) •
        ∑ y ∈ (Finset.univ : Finset Λ).filter (G.Adj x), spinSDot x y N from by
    rw [← Finset.sum_filter]
    rw [Finset.smul_sum]]
  rw [← SimpleGraph.neighborFinset_eq_filter]

/-! ## One-sided bipartite sums -/

/-- On a bipartite graph, the sum of local stars over the complement of one
side equals the sum over that side.  The proof swaps each oriented adjacent pair
and uses `spinSDot_comm`. -/
theorem sum_graphLocalClusterHamiltonianS_filter_not_eq_filter_of_bipartite
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {A : Λ → Prop} [DecidablePred A]
    (hA : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y) (N : ℕ) :
    ∑ x ∈ (Finset.univ : Finset Λ).filter (fun x => ¬ A x),
        graphLocalClusterHamiltonianS G x N =
      ∑ x ∈ (Finset.univ : Finset Λ).filter A,
        graphLocalClusterHamiltonianS G x N := by
  classical
  unfold graphLocalClusterHamiltonianS
  rw [← Finset.sum_sigma
      (s := (Finset.univ : Finset Λ).filter (fun x => ¬ A x))
      (t := fun x => G.neighborFinset x)
      (f := fun p : Sigma fun _ : Λ => Λ => spinSDot p.1 p.2 N),
    ← Finset.sum_sigma
      (s := (Finset.univ : Finset Λ).filter A)
      (t := fun x => G.neighborFinset x)
      (f := fun p : Sigma fun _ : Λ => Λ => spinSDot p.1 p.2 N)]
  refine Finset.sum_bij
    (fun p _ => (⟨p.2, p.1⟩ : Sigma fun _ : Λ => Λ)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp ⊢
    rcases hp with ⟨hpx, hpy⟩
    have hp_notA : ¬ A p.1 := by simpa using hpx
    have h_adj : G.Adj p.1 p.2 := (SimpleGraph.mem_neighborFinset G p.1 p.2).mp hpy
    have hp2A : A p.2 := by
      by_contra hp2_notA
      exact hA h_adj (propext (Iff.intro (fun hp1A => False.elim (hp_notA hp1A))
        (fun hp2A => False.elim (hp2_notA hp2A))))
    constructor
    · simp [hp2A]
    · exact (SimpleGraph.mem_neighborFinset G p.2 p.1).mpr (G.symm h_adj)
  · intro p₁ hp₁ p₂ hp₂ hswap
    cases p₁
    cases p₂
    simp only [Sigma.mk.injEq, heq_eq_eq] at hswap ⊢
    exact ⟨hswap.2, hswap.1⟩
  · intro q hq
    refine ⟨(⟨q.2, q.1⟩ : Sigma fun _ : Λ => Λ), ?_, ?_⟩
    · rw [Finset.mem_sigma] at hq ⊢
      rcases hq with ⟨hqx, hqy⟩
      have hqA : A q.1 := by simpa using hqx
      have h_adj : G.Adj q.1 q.2 := (SimpleGraph.mem_neighborFinset G q.1 q.2).mp hqy
      have hq2_notA : ¬ A q.2 := by
        intro hq2A
        exact hA h_adj (propext (Iff.intro (fun _ => hq2A) (fun _ => hqA)))
      constructor
      · simp [hq2_notA]
      · exact (SimpleGraph.mem_neighborFinset G q.2 q.1).mpr (G.symm h_adj)
    · simp
  · intro p hp
    exact spinSDot_comm p.1 p.2 N

/-- On a bipartite graph, the all-vertex local-star sum is twice the
one-sided sum over a chosen bipartition side. -/
theorem sum_graphLocalClusterHamiltonianS_eq_two_smul_filter_of_bipartite
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {A : Λ → Prop} [DecidablePred A]
    (hA : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y) (N : ℕ) :
    ∑ x : Λ, graphLocalClusterHamiltonianS G x N =
      (2 : ℂ) •
        ∑ x ∈ (Finset.univ : Finset Λ).filter A,
          graphLocalClusterHamiltonianS G x N := by
  classical
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset Λ)) A
      (fun x => graphLocalClusterHamiltonianS G x N)).symm
  have hnot :=
    sum_graphLocalClusterHamiltonianS_filter_not_eq_filter_of_bipartite
      G hA N
  calc
    ∑ x : Λ, graphLocalClusterHamiltonianS G x N =
        ∑ x ∈ (Finset.univ : Finset Λ).filter A,
            graphLocalClusterHamiltonianS G x N +
          ∑ x ∈ (Finset.univ : Finset Λ).filter (fun x => ¬ A x),
            graphLocalClusterHamiltonianS G x N := hsplit
    _ = ∑ x ∈ (Finset.univ : Finset Λ).filter A,
            graphLocalClusterHamiltonianS G x N +
          ∑ x ∈ (Finset.univ : Finset Λ).filter A,
            graphLocalClusterHamiltonianS G x N := by rw [hnot]
    _ = (2 : ℂ) •
        ∑ x ∈ (Finset.univ : Finset Λ).filter A,
          graphLocalClusterHamiltonianS G x N := by
      rw [two_smul]

/-- With coupling `1 / 2`, the graph Hamiltonian on a bipartite graph is exactly
the one-sided sum of local star Hamiltonians over either chosen side. -/
theorem heisenbergHamiltonianOnGraphS_half_eq_sum_filter_graphLocalClusterHamiltonianS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {A : Λ → Prop} [DecidablePred A]
    (hA : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y) (N : ℕ) :
    heisenbergHamiltonianOnGraphS G ((1 : ℂ) / 2) N =
      ∑ x ∈ (Finset.univ : Finset Λ).filter A,
        graphLocalClusterHamiltonianS G x N := by
  rw [heisenbergHamiltonianOnGraphS_half_eq_sum_half_graphLocalClusterHamiltonianS]
  rw [← Finset.smul_sum]
  rw [sum_graphLocalClusterHamiltonianS_eq_two_smul_filter_of_bipartite G hA N]
  rw [smul_smul]
  norm_num

end LatticeSystem.Quantum
