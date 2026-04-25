/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges

/-!
# Hubbard model — graph-centric wrappers, chain and cycle instances

Extracted from `JordanWigner/Hubbard.lean` (tracked in #390). This sub-file
contains:

1. **Graph-centric wrappers** — `hubbardKineticOnGraph`, `hubbardHamiltonianOnGraph`
   and their Hermiticity + `N̂` commutativity.
2. **1D open chain instance** — `hubbardChainHamiltonian`, its Gibbs state,
   and a full Gibbs expectation companion family.
3. **Hubbard Gibbs state on a graph** — `hubbardGibbsStateOnGraph` and bridge
   theorem to the chain.
4. **1D periodic chain instance** — `hubbardCycleHamiltonian`, its Gibbs state,
   and a full Gibbs expectation companion family.
5. **Two-particle eigenstate** — `fermionTotalNumber_mulVec_twoParticle`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Hubbard-on-graph wrappers (graph-centric Hubbard) -/

/-- Hubbard kinetic operator with hopping matrix derived from a
`SimpleGraph G` and uniform edge weight `J : ℂ`. -/
noncomputable def hubbardKineticOnGraph (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (LatticeSystem.Lattice.couplingOf G J)

/-- The graph-built Hubbard kinetic operator commutes with `N̂`. -/
theorem hubbardKineticOnGraph_commute_fermionTotalNumber
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J : ℂ) :
    Commute (hubbardKineticOnGraph N G J)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardKinetic_commute_fermionTotalNumber N _

/-- The graph-built Hubbard kinetic operator is Hermitian when
`J` is real: the coupling `couplingOf G J` is then a Hermitian
matrix on the (symmetric, decidable) graph. -/
theorem hubbardKineticOnGraph_isHermitian
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) :
    (hubbardKineticOnGraph N G J).IsHermitian := by
  unfold hubbardKineticOnGraph
  refine hubbardKinetic_isHermitian N (fun i j => ?_)
  rw [LatticeSystem.Lattice.couplingOf_real G hJ,
    LatticeSystem.Lattice.couplingOf_symm]

/-- The full Hubbard Hamiltonian with hopping derived from a
`SimpleGraph G` plus on-site interaction `U`. -/
noncomputable def hubbardHamiltonianOnGraph (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKineticOnGraph N G J + hubbardOnSiteInteraction N U

/-- The graph-built Hubbard Hamiltonian commutes with `N̂`. -/
theorem hubbardHamiltonianOnGraph_commute_fermionTotalNumber
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    Commute (hubbardHamiltonianOnGraph N G J U)
      (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHamiltonianOnGraph
  exact (hubbardKineticOnGraph_commute_fermionTotalNumber N G J).add_left
    (hubbardOnSiteInteraction_commute_fermionTotalNumber N U)

/-- The graph-built Hubbard Hamiltonian is Hermitian when both
`J` and `U` are real. -/
theorem hubbardHamiltonianOnGraph_isHermitian
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J U : ℂ} (hJ : star J = J) (hU : star U = U) :
    (hubbardHamiltonianOnGraph N G J U).IsHermitian := by
  unfold hubbardHamiltonianOnGraph
  exact (hubbardKineticOnGraph_isHermitian N G hJ).add
    (hubbardOnSiteInteraction_isHermitian N hU)

/-! ## 1D Hubbard chain instance -/

/-- The canonical 1D nearest-neighbour Hubbard Hamiltonian on a
chain of `N + 1` spinful sites, with hopping amplitude `J : ℝ`
(ferromagnetic sign convention `−J`) and on-site Coulomb
repulsion `U : ℝ`. -/
noncomputable def hubbardChainHamiltonian (N : ℕ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N (SimpleGraph.pathGraph (N + 1))
    (-(J : ℂ)) (U : ℂ)

/-- The 1D Hubbard chain Hamiltonian is Hermitian. -/
theorem hubbardChainHamiltonian_isHermitian (N : ℕ) (J U : ℝ) :
    (hubbardChainHamiltonian N J U).IsHermitian :=
  hubbardHamiltonianOnGraph_isHermitian N _ (by simp) (by simp)

/-- The 1D Hubbard chain Hamiltonian commutes with `N̂` (charge
conservation). -/
theorem hubbardChainHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (J U : ℝ) :
    Commute (hubbardChainHamiltonian N J U)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardHamiltonianOnGraph_commute_fermionTotalNumber N _ _ _

/-- `hubbardHamiltonianOnGraph` annihilates the vacuum. Both
`hubbardKinetic` and `hubbardOnSiteInteraction` do, by PR #166. -/
theorem hubbardHamiltonianOnGraph_mulVec_vacuum
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    (hubbardHamiltonianOnGraph N G J U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardHamiltonianOnGraph hubbardKineticOnGraph
  rw [Matrix.add_mulVec, hubbardKinetic_mulVec_vacuum,
    hubbardOnSiteInteraction_mulVec_vacuum, add_zero]

/-- The 1D Hubbard chain Hamiltonian annihilates the vacuum. Free
corollary of `hubbardHamiltonianOnGraph_mulVec_vacuum`. -/
theorem hubbardChainHamiltonian_mulVec_vacuum
    (N : ℕ) (J U : ℝ) :
    (hubbardChainHamiltonian N J U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  hubbardHamiltonianOnGraph_mulVec_vacuum N _ _ _

/-- The Gibbs state of the 1D Hubbard chain Hamiltonian. -/
noncomputable def hubbardChainGibbsState (N : ℕ) (β : ℝ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardChainHamiltonian N J U)

/-- The 1D Hubbard chain Gibbs state is Hermitian. -/
theorem hubbardChainGibbsState_isHermitian (N : ℕ) (β : ℝ) (J U : ℝ) :
    (hubbardChainGibbsState N β J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- The 1D Hubbard chain Gibbs state commutes with its
Hamiltonian. -/
theorem hubbardChainGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (J U : ℝ) :
    Commute (hubbardChainGibbsState N β J U)
      (hubbardChainHamiltonian N J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-! ## Hubbard chain Gibbs expectation companions

Generic-`gibbsExpectation*` lemmas instantiated at the 1D Hubbard
chain Hamiltonian. -/

/-- Infinite-temperature (β = 0) closed form for the Hubbard
chain expectation: `⟨A⟩_0 = (1/dim) · Tr A`. -/
theorem hubbardChainGibbsExpectation_zero (N : ℕ) (J U : ℝ)
    (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation 0
        (hubbardChainHamiltonian N J U) A
      = ((Fintype.card (Fin (2 * N + 2) → Fin 2) : ℂ))⁻¹ *
          A.trace :=
  LatticeSystem.Quantum.gibbsExpectation_zero
    (hubbardChainHamiltonian N J U) A

/-- For Hermitian `O`, the Hubbard-chain expectation `⟨O⟩_β` is
real. -/
theorem hubbardChainGibbsExpectation_im_of_isHermitian
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U) O).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_im_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) hO β

/-- Hubbard-chain conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem hubbardChainGibbsExpectation_commutator_hamiltonian
    (N : ℕ) (β J U : ℝ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U)
        (hubbardChainHamiltonian N J U * A
          - A * hubbardChainHamiltonian N J U) = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_commutator_hamiltonian β
    (hubbardChainHamiltonian N J U) A

/-- Hubbard-chain energy expectation is real:
`(⟨H_chain⟩_β).im = 0`. -/
theorem hubbardChainGibbsExpectation_hamiltonian_im
    (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U)
        (hubbardChainHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_hamiltonian_im
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- Hubbard-chain energy n-th power expectation is real:
`(⟨H_chain^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem hubbardChainGibbsExpectation_hamiltonian_pow_im
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U)
        ((hubbardChainHamiltonian N J U)^n)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_pow_im_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U)
    (hubbardChainHamiltonian_isHermitian N J U) β n

/-- Hubbard-chain partition function is real. -/
theorem hubbardChain_partitionFn_im (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.partitionFn β
        (hubbardChainHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.partitionFn_im_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- Hubbard-chain real-cast equality. -/
theorem hubbardChainGibbsExpectation_ofReal_re_eq
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (((LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U) O).re : ℂ))
      = LatticeSystem.Quantum.gibbsExpectation β
          (hubbardChainHamiltonian N J U) O :=
  LatticeSystem.Quantum.gibbsExpectation_ofReal_re_eq_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) hO β

/-- Hubbard-chain Rényi-n trace identity. -/
theorem hubbardChainGibbsState_pow_trace
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    ((hubbardChainGibbsState N β J U)^n).trace
      = LatticeSystem.Quantum.partitionFn ((n : ℝ) * β)
          (hubbardChainHamiltonian N J U)
        / (LatticeSystem.Quantum.partitionFn β
            (hubbardChainHamiltonian N J U)) ^ n :=
  LatticeSystem.Quantum.gibbsState_pow_trace β
    (hubbardChainHamiltonian N J U) n

/-- The two-particle state `c_i† c_j† |vac⟩` is an `N̂`-eigenstate
with eigenvalue 2. The Leibniz rule
`[N̂, AB] = [N̂,A]B + A[N̂,B]` together with `[N̂, c_†] = c_†`
yields `[N̂, c_i† c_j†] = 2 c_i† c_j†`; applied to the vacuum and
combined with `N̂ |vac⟩ = 0` this gives the eigenvalue 2. -/
theorem fermionTotalNumber_mulVec_twoParticle
    (N : ℕ) (i j : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N)) =
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N) := by
  rw [Matrix.mulVec_mulVec]
  have h₁ : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N i)).trans
      (add_comm _ _)
  have h₂ : fermionTotalNumber N * fermionMultiCreation N j =
      fermionMultiCreation N j * fermionTotalNumber N +
        fermionMultiCreation N j :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N j)).trans
      (add_comm _ _)
  have h_comm : fermionTotalNumber N *
      (fermionMultiCreation N i * fermionMultiCreation N j) =
      (fermionMultiCreation N i * fermionMultiCreation N j) *
        fermionTotalNumber N +
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j) := by
    calc fermionTotalNumber N *
          (fermionMultiCreation N i * fermionMultiCreation N j)
        = (fermionTotalNumber N * fermionMultiCreation N i) *
            fermionMultiCreation N j := by rw [← Matrix.mul_assoc]
      _ = (fermionMultiCreation N i * fermionTotalNumber N +
            fermionMultiCreation N i) * fermionMultiCreation N j := by
            rw [h₁]
      _ = fermionMultiCreation N i * fermionTotalNumber N *
            fermionMultiCreation N j +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.add_mul]
      _ = fermionMultiCreation N i *
            (fermionTotalNumber N * fermionMultiCreation N j) +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.mul_assoc]
      _ = fermionMultiCreation N i *
            (fermionMultiCreation N j * fermionTotalNumber N +
              fermionMultiCreation N j) +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [h₂]
      _ = fermionMultiCreation N i *
            (fermionMultiCreation N j * fermionTotalNumber N) +
          fermionMultiCreation N i * fermionMultiCreation N j +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.mul_add]
      _ = fermionMultiCreation N i * fermionMultiCreation N j *
            fermionTotalNumber N +
          (fermionMultiCreation N i * fermionMultiCreation N j +
            fermionMultiCreation N i * fermionMultiCreation N j) := by
            rw [← Matrix.mul_assoc]; abel
      _ = fermionMultiCreation N i * fermionMultiCreation N j *
            fermionTotalNumber N +
          (2 : ℂ) •
            (fermionMultiCreation N i * fermionMultiCreation N j) := by
            rw [two_smul]
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalNumber_mulVec_vacuum, Matrix.mulVec_zero, zero_add,
    Matrix.smul_mulVec]

/-! ## Hubbard Gibbs state on a graph -/

/-- Gibbs state of the graph-built Hubbard Hamiltonian. -/
noncomputable def hubbardGibbsStateOnGraph (N : ℕ) (β : ℝ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardHamiltonianOnGraph N G J U)

/-- Hermiticity of the graph-built Hubbard Gibbs state. -/
theorem hubbardGibbsStateOnGraph_isHermitian
    (N : ℕ) (β : ℝ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J U : ℂ} (hJ : star J = J) (hU : star U = U) :
    (hubbardGibbsStateOnGraph N β G J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardHamiltonianOnGraph_isHermitian N G hJ hU) β

/-- The graph-built Hubbard Gibbs state commutes with its Hamiltonian. -/
theorem hubbardGibbsStateOnGraph_commute_hamiltonian
    (N : ℕ) (β : ℝ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    Commute (hubbardGibbsStateOnGraph N β G J U)
      (hubbardHamiltonianOnGraph N G J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-- Bridge: `hubbardChainGibbsState` = `hubbardGibbsStateOnGraph`
on `pathGraph (N+1)` with weight `-J`. -/
theorem hubbardChainGibbsState_eq_onGraph (N : ℕ) (β : ℝ) (J U : ℝ) :
    hubbardChainGibbsState N β J U
      = hubbardGibbsStateOnGraph N β (SimpleGraph.pathGraph (N + 1))
          (-(J : ℂ)) (U : ℂ) :=
  rfl

/-! ## Periodic 1D Hubbard chain (cycleGraph instance) -/

/-- The canonical 1D periodic Hubbard ring on `N + 1` spinful sites,
defined via `hubbardHamiltonianOnGraph` with the cycle graph on
`N + 1` vertices. -/
noncomputable def hubbardCycleHamiltonian (N : ℕ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N (SimpleGraph.cycleGraph (N + 1))
    (-(J : ℂ)) (U : ℂ)

/-- Hermiticity of the periodic Hubbard chain. -/
theorem hubbardCycleHamiltonian_isHermitian (N : ℕ) (J U : ℝ) :
    (hubbardCycleHamiltonian N J U).IsHermitian :=
  hubbardHamiltonianOnGraph_isHermitian N _ (by simp) (by simp)

/-- Charge conservation for the periodic Hubbard chain. -/
theorem hubbardCycleHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (J U : ℝ) :
    Commute (hubbardCycleHamiltonian N J U)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardHamiltonianOnGraph_commute_fermionTotalNumber N _ _ _

/-- Gibbs state of the periodic Hubbard chain. -/
noncomputable def hubbardCycleGibbsState (N : ℕ) (β : ℝ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardCycleHamiltonian N J U)

/-- Hermiticity of the periodic Hubbard Gibbs state. -/
theorem hubbardCycleGibbsState_isHermitian (N : ℕ) (β : ℝ) (J U : ℝ) :
    (hubbardCycleGibbsState N β J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) β

/-- The periodic Hubbard Gibbs state commutes with the periodic
Hubbard Hamiltonian. The dual companion of
`hubbardChainGibbsState_commute_hamiltonian` (open chain). -/
theorem hubbardCycleGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (J U : ℝ) :
    Commute (hubbardCycleGibbsState N β J U)
      (hubbardCycleHamiltonian N J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β
    (hubbardCycleHamiltonian N J U)

/-! ## Periodic Hubbard chain Gibbs expectation companions -/

/-- Infinite-temperature (β = 0) closed form for the periodic
Hubbard expectation. -/
theorem hubbardCycleGibbsExpectation_zero (N : ℕ) (J U : ℝ)
    (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation 0
        (hubbardCycleHamiltonian N J U) A
      = ((Fintype.card (Fin (2 * N + 2) → Fin 2) : ℂ))⁻¹ *
          A.trace :=
  LatticeSystem.Quantum.gibbsExpectation_zero
    (hubbardCycleHamiltonian N J U) A

/-- For Hermitian `O`, the periodic-Hubbard expectation `⟨O⟩_β`
is real. -/
theorem hubbardCycleGibbsExpectation_im_of_isHermitian
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U) O).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_im_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) hO β

/-- Periodic-Hubbard conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem hubbardCycleGibbsExpectation_commutator_hamiltonian
    (N : ℕ) (β J U : ℝ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U)
        (hubbardCycleHamiltonian N J U * A
          - A * hubbardCycleHamiltonian N J U) = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_commutator_hamiltonian β
    (hubbardCycleHamiltonian N J U) A

/-- Periodic-Hubbard energy expectation is real. -/
theorem hubbardCycleGibbsExpectation_hamiltonian_im
    (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U)
        (hubbardCycleHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_hamiltonian_im
    (hubbardCycleHamiltonian_isHermitian N J U) β

/-- Periodic-Hubbard energy n-th power expectation is real. -/
theorem hubbardCycleGibbsExpectation_hamiltonian_pow_im
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U)
        ((hubbardCycleHamiltonian N J U)^n)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_pow_im_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U)
    (hubbardCycleHamiltonian_isHermitian N J U) β n

/-- Periodic-Hubbard partition function is real. -/
theorem hubbardCycle_partitionFn_im (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.partitionFn β
        (hubbardCycleHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.partitionFn_im_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) β

/-- Periodic-Hubbard real-cast equality. -/
theorem hubbardCycleGibbsExpectation_ofReal_re_eq
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (((LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U) O).re : ℂ))
      = LatticeSystem.Quantum.gibbsExpectation β
          (hubbardCycleHamiltonian N J U) O :=
  LatticeSystem.Quantum.gibbsExpectation_ofReal_re_eq_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) hO β

/-- Periodic-Hubbard Rényi-n trace identity. -/
theorem hubbardCycleGibbsState_pow_trace
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    ((hubbardCycleGibbsState N β J U)^n).trace
      = LatticeSystem.Quantum.partitionFn ((n : ℝ) * β)
          (hubbardCycleHamiltonian N J U)
        / (LatticeSystem.Quantum.partitionFn β
            (hubbardCycleHamiltonian N J U)) ^ n :=
  LatticeSystem.Quantum.gibbsState_pow_trace β
    (hubbardCycleHamiltonian N J U) n

end LatticeSystem.Fermion
