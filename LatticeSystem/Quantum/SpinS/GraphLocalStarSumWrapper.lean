import LatticeSystem.Quantum.SpinS.GraphLocalStarLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueSumLower
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.SingleClusterGSJointWitness

/-!
# Option-star and graph-local sum lower bounds

This file completes the next Tasaki §2.5 Problem 2.5.b bridge: it transports
the Problem 2.5.a single-cluster minimum-eigenvalue formula to the canonical
option-star Hamiltonian, feeds that Rayleigh lower bound into the graph-local
block decomposition, and packages the finite-sum lower bound for the one-sided
bipartite graph decomposition.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497, using Problem 2.5.a, pp. 38,
  496-497, and Lemma A.5, p. 468.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {α β Λ : Type*}

/-! ## Option-star transport of the single-cluster lower bound -/

/-- Transported single-cluster Hamiltonians are Hermitian. -/
theorem transportedSingleClusterHamiltonianS_isHermitian
    (z N : ℕ) (e : Fin (z + 1) ≃ β) :
    (transportedSingleClusterHamiltonianS z N e).IsHermitian := by
  unfold transportedSingleClusterHamiltonianS
  exact (singleClusterHamiltonianS_isHermitian z N).reindex (siteConfigEquiv e N)

/-- The canonical option-star Hamiltonian is Hermitian. -/
theorem optionClusterHamiltonianS_isHermitian
    [DecidableEq α] (s : Finset α) (N : ℕ) :
    (optionClusterHamiltonianS s N).IsHermitian := by
  rw [← transportedSingleClusterHamiltonianS_option_eq s N]
  exact transportedSingleClusterHamiltonianS_isHermitian s.card N
    (singleClusterOptionEquiv s)

/-- Pulling both entries of a dot product forward along an equivalence leaves the
dot product unchanged. -/
theorem dotProduct_comp_equiv
    [Fintype α] [Fintype β] (e : α ≃ β) (v : β → ℂ) :
    dotProduct (star (v ∘ e)) (v ∘ e) = dotProduct (star v) v := by
  simpa using dotProduct_comp_equiv_symm e.symm v

/-- Reindexing a matrix and pushing a vector forward along the same equivalence
does not change its Rayleigh numerator. -/
theorem rayleighOnVec_reindex_comp
    [Fintype α] [Fintype β] (e : α ≃ β) (M : Matrix α α ℂ) (v : β → ℂ) :
    rayleighOnVec (Matrix.reindex e e M) v = rayleighOnVec M (v ∘ e) := by
  simpa [Function.comp_def] using rayleighOnVec_reindex_comp_symm e M (v ∘ e)

/-- The Problem 2.5.a single-cluster ground energy gives a Rayleigh lower bound
for the canonical option-star Hamiltonian. -/
theorem optionClusterHamiltonianS_rayleigh_lower_singleClusterGSEnergy
    [IsAlgClosed ℂ] [DecidableEq α] (s : Finset α) (N : ℕ)
    (hs : 1 ≤ s.card) (w : (Option s → Fin (N + 1)) → ℂ) :
    (singleClusterGSEnergyS s.card N).re *
        (dotProduct (star w) w).re ≤
      rayleighOnVec (optionClusterHamiltonianS s N) w := by
  let eSite := singleClusterOptionEquiv s
  let eCfg := siteConfigEquiv eSite N
  let v : (Fin (s.card + 1) → Fin (N + 1)) → ℂ := w ∘ eCfg
  have hvar :=
    hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec
      (singleClusterHamiltonianS_isHermitian s.card N) v
  have hmin :=
    singleClusterHamiltonianS_minEigenvalue_eq_gs_of_predicted_joint_witness
      (z := s.card) N hs
  rw [hmin] at hvar
  have hnorm :
      (dotProduct (star v) v).re = (dotProduct (star w) w).re := by
    dsimp [v, eCfg]
    rw [dotProduct_comp_equiv]
  have hray :
      rayleighOnVec (singleClusterHamiltonianS s.card N) v =
        rayleighOnVec (optionClusterHamiltonianS s N) w := by
    rw [← transportedSingleClusterHamiltonianS_option_eq s N]
    dsimp [v, eCfg, eSite]
    unfold transportedSingleClusterHamiltonianS
    rw [rayleighOnVec_reindex_comp]
  rwa [hnorm, hray] at hvar

/-! ## Graph-local and one-sided bipartite sum wrappers -/

variable [Fintype Λ] [DecidableEq Λ]

/-- Problem 2.5.a gives the graph-local star minimum-eigenvalue lower bound once
the center has at least one graph neighbour. -/
theorem graphLocalClusterHamiltonianS_minEigenvalue_lower_singleClusterGSEnergy
    [IsAlgClosed ℂ] (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ)
    (hx : 1 ≤ (G.neighborFinset x).card) :
    (singleClusterGSEnergyS (G.neighborFinset x).card N).re ≤
      hermitianMinEigenvalue (graphLocalClusterHamiltonianS_isHermitian G x N) := by
  refine graphLocalClusterHamiltonianS_minEigenvalue_lower G x N ?_
  intro _η w
  exact optionClusterHamiltonianS_rayleigh_lower_singleClusterGSEnergy
    (G.neighborFinset x) N hx w

/-- Finite-sum Problem 2.5.b lower bound for any chosen family of graph-local
stars with positive local degree. -/
theorem tasaki25b_graphLocalCluster_sum_lower_bound
    [IsAlgClosed ℂ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (s : Finset Λ) (N : ℕ)
    (hdeg : ∀ x ∈ s, 1 ≤ (G.neighborFinset x).card) :
    ∑ x ∈ s, (singleClusterGSEnergyS (G.neighborFinset x).card N).re ≤
      hermitianMinEigenvalue
        (isHermitian_sum s (fun x => graphLocalClusterHamiltonianS G x N)
          (fun x _hx => graphLocalClusterHamiltonianS_isHermitian G x N)) := by
  refine sum_lower_bounds_le_hermitianMinEigenvalue_sum s
    (fun x => graphLocalClusterHamiltonianS G x N)
    (fun x => (singleClusterGSEnergyS (G.neighborFinset x).card N).re)
    (fun x _hx => graphLocalClusterHamiltonianS_isHermitian G x N) ?_
  intro x hx
  exact graphLocalClusterHamiltonianS_minEigenvalue_lower_singleClusterGSEnergy
    G x N (hdeg x hx)

/-- One-sided bipartite Problem 2.5.b lower bound for the half-coupling graph
Hamiltonian, using the decomposition into graph-local stars over one side of the
bipartition. -/
theorem tasaki25b_heisenbergHamiltonianOnGraphS_half_lower_bound
    [IsAlgClosed ℂ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    {A : Λ → Prop} [DecidablePred A]
    (hA : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y) (N : ℕ)
    (hdeg : ∀ x ∈ (Finset.univ : Finset Λ).filter A,
      1 ≤ (G.neighborFinset x).card) :
    ∑ x ∈ (Finset.univ : Finset Λ).filter A,
        (singleClusterGSEnergyS (G.neighborFinset x).card N).re ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian G
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) N) := by
  classical
  let s : Finset Λ := (Finset.univ : Finset Λ).filter A
  let localH : Λ → Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ :=
    fun x => graphLocalClusterHamiltonianS G x N
  let ε : Λ → ℝ :=
    fun x => (singleClusterGSEnergyS (G.neighborFinset x).card N).re
  let hGraph :=
    heisenbergHamiltonianOnGraphS_isHermitian G
      (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) N
  obtain ⟨v, hunit, hv⟩ :=
    exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue hGraph
  have hterm : ∀ x ∈ s, ε x ≤ rayleighOnVec (localH x) v := by
    intro x hx
    exact le_trans
      (graphLocalClusterHamiltonianS_minEigenvalue_lower_singleClusterGSEnergy
        G x N (hdeg x hx))
      (hermitianMinEigenvalue_le_rayleighOnVec_of_unit
        (graphLocalClusterHamiltonianS_isHermitian G x N) hunit)
  have hsum :
      ∑ x ∈ s, ε x ≤ ∑ x ∈ s, rayleighOnVec (localH x) v :=
    Finset.sum_le_sum hterm
  have hdecomp :
      heisenbergHamiltonianOnGraphS G ((1 : ℂ) / 2) N =
        ∑ x ∈ s, localH x := by
    dsimp [s, localH]
    exact heisenbergHamiltonianOnGraphS_half_eq_sum_filter_graphLocalClusterHamiltonianS
      G hA N
  calc
    ∑ x ∈ (Finset.univ : Finset Λ).filter A,
        (singleClusterGSEnergyS (G.neighborFinset x).card N).re =
        ∑ x ∈ s, ε x := rfl
    _ ≤ ∑ x ∈ s, rayleighOnVec (localH x) v := hsum
    _ = rayleighOnVec (∑ x ∈ s, localH x) v :=
        (rayleighOnVec_sum_matrix s localH v).symm
    _ = rayleighOnVec (heisenbergHamiltonianOnGraphS G ((1 : ℂ) / 2) N) v := by
        rw [hdecomp]
    _ = hermitianMinEigenvalue hGraph := hv

end LatticeSystem.Quantum
