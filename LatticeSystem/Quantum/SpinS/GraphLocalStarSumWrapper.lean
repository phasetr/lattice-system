import LatticeSystem.Quantum.SpinS.GraphLocalStarLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueSumLower
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.SingleClusterGSJointWitness

/-!
# Option-star and graph-local sum lower bounds

This file completes the Tasaki §2.5 Problem 2.5.b chain: it transports the
Problem 2.5.a single-cluster minimum-eigenvalue formula to the canonical
option-star Hamiltonian, feeds that Rayleigh lower bound into the graph-local
block decomposition, sums the local bounds through the minimum-eigenvalue form
of Lemma A.5, and concludes the Anderson lower bound on the ground-state energy
of the antiferromagnetic Heisenberg Hamiltonian (2.5.1) on a bipartite lattice.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution pp. 497-498, using Problem 2.5.a, pp. 38,
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

/-- Problem 2.5.a bounds the minimum eigenvalue of the graph-local star at any
centre, with no condition on the local degree.

For a centre with at least one graph neighbour the bound is the Problem 2.5.a
ground energy transported to the graph-local star.  For an isolated centre the
star Hamiltonian is the zero matrix, so its minimum eigenvalue is `0`, while the
Problem 2.5.a expression evaluates to `-(N / 2) ≤ 0`; the bound therefore holds
with slack.  Only the inequality survives at an isolated centre: the Problem
2.5.a equality itself fails there, since its derivation evaluates `min {zS, S}`
as `S`, which requires `1 ≤ z`.

References: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.a, p. 38, solution pp. 496-497. -/
theorem graphLocalClusterHamiltonianS_minEigenvalue_lower_singleClusterGSEnergy
    [IsAlgClosed ℂ] (G : SimpleGraph Λ) [DecidableRel G.Adj] (x : Λ) (N : ℕ) :
    (singleClusterGSEnergyS (G.neighborFinset x).card N).re ≤
      hermitianMinEigenvalue (graphLocalClusterHamiltonianS_isHermitian G x N) := by
  by_cases hx : 1 ≤ (G.neighborFinset x).card
  · refine graphLocalClusterHamiltonianS_minEigenvalue_lower G x N ?_
    intro _η w
    exact optionClusterHamiltonianS_rayleigh_lower_singleClusterGSEnergy
      (G.neighborFinset x) N hx w
  · have hcard : (G.neighborFinset x).card = 0 := by omega
    have hzero : graphLocalClusterHamiltonianS G x N = 0 := by
      unfold graphLocalClusterHamiltonianS
      rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
    obtain ⟨v, _hunit, hv⟩ :=
      exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue
        (graphLocalClusterHamiltonianS_isHermitian G x N)
    have hray : rayleighOnVec (graphLocalClusterHamiltonianS G x N) v = 0 := by
      rw [hzero]
      simp [rayleighOnVec]
    rw [hray] at hv
    rw [hcard, singleClusterGSEnergyS_re_eq, ← hv]
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith

/-- Finite-sum Problem 2.5.b lower bound for any chosen family of graph-local
stars, with no condition on the local degrees.

This is the minimum-eigenvalue form of Tasaki's Lemma A.5 (p. 468), applied to
the star Hamiltonians of the chosen family; the hint of Problem 2.5.b is exactly
that this step needs no commutation between the summands.

References: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.b, p. 38, solution pp. 497-498, Lemma A.5, p. 468. -/
theorem tasaki25b_graphLocalCluster_sum_lower_bound
    [IsAlgClosed ℂ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (s : Finset Λ) (N : ℕ) :
    ∑ x ∈ s, (singleClusterGSEnergyS (G.neighborFinset x).card N).re ≤
      hermitianMinEigenvalue
        (Matrix.isHermitian_sum s
          (fun x _hx => graphLocalClusterHamiltonianS_isHermitian G x N)) := by
  refine sum_lower_bounds_le_hermitianMinEigenvalue_sum s
    (fun x => graphLocalClusterHamiltonianS G x N)
    (fun x => (singleClusterGSEnergyS (G.neighborFinset x).card N).re)
    (fun x _hx => graphLocalClusterHamiltonianS_isHermitian G x N) ?_
  intro x _hx
  exact graphLocalClusterHamiltonianS_minEigenvalue_lower_singleClusterGSEnergy
    G x N

/-- **Tasaki Problem 2.5.b**: the Anderson lower bound on the ground-state
energy of the antiferromagnetic Heisenberg model on a bipartite lattice.

With `hA` saying that every bond of `G` joins `A` to its complement, and with
`S = N / 2`, the ground-state energy of the Hamiltonian
`Ĥ = ∑_{{x,y}∈B} Ŝ_x · Ŝ_y` of eq. (2.5.1) satisfies
`E_GS ≥ -∑_{x∈A} S (1 + |N(x)| S)`.

The graph Hamiltonian here sums over ordered pairs, so each undirected bond is
counted twice; the coupling `1 / 2` is therefore the unit coupling per bond of
(2.5.1), not a weakened model.

The proof decomposes `Ĥ` as the sum of the star Hamiltonians `ĥ_x` over the
chosen sublattice, bounds each star by Problem 2.5.a, and adds those bounds
through the minimum-eigenvalue form of Lemma A.5, which needs no commutation
between the summands.

No hypothesis restricts the local degrees: an isolated site of `A` contributes a
term that only weakens the bound.  `[IsAlgClosed ℂ]` is an always-satisfiable
instance assumption, discharged at every use site by mathlib's
`Complex.isAlgClosed`; it is carried only because this module's import closure
does not contain that instance, and it is not a hypothesis of the printed
statement.

References: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.b, p. 38, solution pp. 497-498, Problem 2.5.a, p. 38,
and Lemma A.5, p. 468. -/
theorem tasaki_problem_2_5_b_groundEnergy_lower_bound
    [IsAlgClosed ℂ] (G : SimpleGraph Λ) [DecidableRel G.Adj]
    {A : Λ → Prop} [DecidablePred A]
    (hA : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y) (N : ℕ) :
    ∑ x ∈ (Finset.univ : Finset Λ).filter A,
        -((N : ℝ) / 2) * ((G.degree x : ℝ) * (N : ℝ) / 2 + 1) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian G
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) N) := by
  classical
  have hdecomp :
      heisenbergHamiltonianOnGraphS G ((1 : ℂ) / 2) N =
        ∑ x ∈ (Finset.univ : Finset Λ).filter A,
          graphLocalClusterHamiltonianS G x N :=
    heisenbergHamiltonianOnGraphS_half_eq_sum_filter_graphLocalClusterHamiltonianS
      G hA N
  have hsum :=
    tasaki25b_graphLocalCluster_sum_lower_bound G
      ((Finset.univ : Finset Λ).filter A) N
  have heig :
      hermitianMinEigenvalue
          (Matrix.isHermitian_sum ((Finset.univ : Finset Λ).filter A)
            (fun x _hx => graphLocalClusterHamiltonianS_isHermitian G x N)) =
        hermitianMinEigenvalue
          (heisenbergHamiltonianOnGraphS_isHermitian G
            (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) N) :=
    hermitianMinEigenvalue_eq_of_spectrum_eq _ _ (by rw [hdecomp])
  rw [heig] at hsum
  simpa [singleClusterGSEnergyS_re_eq] using hsum

end LatticeSystem.Quantum
