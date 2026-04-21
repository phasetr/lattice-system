/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner
import LatticeSystem.Lattice.Graph

/-!
# Test coverage for Hubbard infrastructure

Backfill regression tests for PRs #135-#172 (Hubbard skeleton on
top of Jordan–Wigner).

## Test types
- **Shim tests**: invoke the named theorem on a small instance.
  Brittle to renames, but serve as signature-preservation guards.
- **Bridge identity tests**: check `def_A = def_B` between two
  parallel APIs. Catches drift between e.g. \`hubbardChainHamiltonian\`
  and \`hubbardHamiltonianOnGraph (pathGraph _) ..\`.
- **`decide`-based graph-pattern tests**: the underlying
  \`pathGraph\` / \`cycleGraph\` adjacency patterns used to construct
  the Hubbard Hamiltonian. Refactor-robust because they don't
  depend on the operator definition.
-/

namespace LatticeSystem.Tests.Hubbard

open LatticeSystem.Fermion LatticeSystem.Lattice LatticeSystem.Quantum
  SimpleGraph

/-! ## fermionHopping / fermionDensityInteraction / fermionGenericHamiltonian -/

/-- Charge conservation for `fermionHopping` on N=0 (single site, the
trivial case). -/
example (t : Fin 1 → Fin 1 → ℂ) :
    Commute (fermionHopping 0 t) (fermionTotalNumber 0) :=
  fermionHopping_commute_fermionTotalNumber 0 t

/-- Charge conservation for `fermionHopping` on N=1. -/
example (t : Fin 2 → Fin 2 → ℂ) :
    Commute (fermionHopping 1 t) (fermionTotalNumber 1) :=
  fermionHopping_commute_fermionTotalNumber 1 t

/-- Hermiticity for `fermionHopping` on N=1 with Hermitian t. -/
example {t : Fin 2 → Fin 2 → ℂ} (ht : ∀ i j, star (t i j) = t j i) :
    (fermionHopping 1 t).IsHermitian :=
  fermionHopping_isHermitian 1 ht

/-- Charge conservation for `fermionDensityInteraction` on N=1. -/
example (V : Fin 2 → Fin 2 → ℂ) :
    Commute (fermionDensityInteraction 1 V) (fermionTotalNumber 1) :=
  fermionDensityInteraction_commute_fermionTotalNumber 1 V

/-- Hermiticity for `fermionDensityInteraction` on N=1 with real V. -/
example {V : Fin 2 → Fin 2 → ℂ} (hV : ∀ i j, star (V i j) = V i j) :
    (fermionDensityInteraction 1 V).IsHermitian :=
  fermionDensityInteraction_isHermitian 1 hV

/-- Generic Hamiltonian commute / Hermiticity on N=1. -/
example (t V : Fin 2 → Fin 2 → ℂ) :
    Commute (fermionGenericHamiltonian 1 t V) (fermionTotalNumber 1) :=
  fermionGenericHamiltonian_commute_fermionTotalNumber 1 t V

example {t V : Fin 2 → Fin 2 → ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hV : ∀ i j, star (V i j) = V i j) :
    (fermionGenericHamiltonian 1 t V).IsHermitian :=
  fermionGenericHamiltonian_isHermitian 1 ht hV

/-! ## Hubbard (spinful) operator shims -/

/-- Spinful kinetic charge conservation on N=0 (1 spinful site = 2
underlying JW positions). -/
example (t : Fin 1 → Fin 1 → ℂ) :
    Commute (hubbardKinetic 0 t) (fermionTotalNumber (2 * 0 + 1)) :=
  hubbardKinetic_commute_fermionTotalNumber 0 t

/-- Spinful kinetic Hermiticity on N=1 (2 spinful sites). -/
example {t : Fin 2 → Fin 2 → ℂ} (ht : ∀ i j, star (t i j) = t j i) :
    (hubbardKinetic 1 t).IsHermitian :=
  hubbardKinetic_isHermitian 1 ht

/-- Hubbard on-site interaction commute on N=1. -/
example (U : ℂ) :
    Commute (hubbardOnSiteInteraction 1 U) (fermionTotalNumber (2 * 1 + 1)) :=
  hubbardOnSiteInteraction_commute_fermionTotalNumber 1 U

/-- Hubbard on-site interaction Hermiticity on N=1 with real U. -/
example {U : ℂ} (hU : star U = U) :
    (hubbardOnSiteInteraction 1 U).IsHermitian :=
  hubbardOnSiteInteraction_isHermitian 1 hU

/-- Full Hubbard Hamiltonian commute / Hermiticity on N=1. -/
example (t : Fin 2 → Fin 2 → ℂ) (U : ℂ) :
    Commute (hubbardHamiltonian 1 t U) (fermionTotalNumber (2 * 1 + 1)) :=
  hubbardHamiltonian_commute_fermionTotalNumber 1 t U

example {t : Fin 2 → Fin 2 → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardHamiltonian 1 t U).IsHermitian :=
  hubbardHamiltonian_isHermitian 1 ht hU

/-- Hubbard Gibbs state Hermiticity on N=1. -/
example (β : ℝ) {t : Fin 2 → Fin 2 → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardGibbsState 1 β t U).IsHermitian :=
  hubbardGibbsState_isHermitian 1 β ht hU

/-! ## Hubbard chain instance -/

/-- 2-site chain Hubbard Hermiticity. -/
example (J U : ℝ) : (hubbardChainHamiltonian 1 J U).IsHermitian :=
  hubbardChainHamiltonian_isHermitian 1 J U

/-- 2-site chain Hubbard charge conservation. -/
example (J U : ℝ) :
    Commute (hubbardChainHamiltonian 1 J U) (fermionTotalNumber (2 * 1 + 1)) :=
  hubbardChainHamiltonian_commute_fermionTotalNumber 1 J U

/-! ## Bridge identity: chain = Hubbard-on-graph(pathGraph) -/

/-- The chain instance equals the graph wrapper applied to `pathGraph`.
This is `rfl`-true by definition (PR #170), so it acts as a
consistency tripwire: any future refactor that breaks the
definitional equality between the two API entry points will fail
this test. -/
example (N : ℕ) (J U : ℝ) :
    hubbardChainHamiltonian N J U =
      hubbardHamiltonianOnGraph N (pathGraph (N + 1))
        (-(J : ℂ)) (U : ℂ) :=
  rfl

/-! ## Underlying graph adjacency: decide-based property tests

These survive any refactor of the operator definitions because they
test only the SimpleGraph adjacency pattern that the kinetic
operator is built from. -/

/-- The 3-site chain (`pathGraph 3`) used by `hubbardChainHamiltonian 2`
has 4 ordered adjacent pairs (= 2 undirected edges). -/
example :
    (Finset.univ.filter (fun p : Fin 3 × Fin 3 => (pathGraph 3).Adj p.1 p.2)).card
      = 4 := by decide

/-- The 4-site cycle (`cycleGraph 4`) has 8 ordered adjacent pairs. -/
example :
    (Finset.univ.filter (fun p : Fin 4 × Fin 4 => (cycleGraph 4).Adj p.1 p.2)).card
      = 8 := by decide

/-! ## Spinful conserved charges (PR #163, #164, #167, #168) -/

/-- N_↑ commutes with N̂ on N=1. -/
example :
    Commute (fermionTotalUpNumber 1) (fermionTotalNumber (2 * 1 + 1)) :=
  fermionTotalUpNumber_commute_fermionTotalNumber 1

/-- N_↓ commutes with N̂ on N=1. -/
example :
    Commute (fermionTotalDownNumber 1) (fermionTotalNumber (2 * 1 + 1)) :=
  fermionTotalDownNumber_commute_fermionTotalNumber 1

/-- N_↑ and N_↓ commute. -/
example :
    Commute (fermionTotalUpNumber 1) (fermionTotalDownNumber 1) :=
  fermionTotalUpNumber_commute_fermionTotalDownNumber 1

/-- S^z_tot commutes with N̂. -/
example :
    Commute (fermionTotalSpinZ 1) (fermionTotalNumber (2 * 1 + 1)) :=
  fermionTotalSpinZ_commute_fermionTotalNumber 1

/-- N_↓ commutes with c_{i↑}†. -/
example (i : Fin 2) :
    Commute (fermionTotalDownNumber 1) (fermionUpCreation 1 i) :=
  fermionTotalDownNumber_commute_fermionUpCreation 1 i

/-! ## Vacuum annihilation (PRs #152-#154, #166) -/

/-- c_i annihilates the vacuum (N=1). -/
example (i : Fin 2) :
    (fermionMultiAnnihilation 1 i).mulVec (fermionMultiVacuum 1) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum 1 i

/-- N̂ annihilates the vacuum. -/
example : (fermionTotalNumber 1).mulVec (fermionMultiVacuum 1) = 0 :=
  fermionTotalNumber_mulVec_vacuum 1

/-- The full Hubbard-skeleton Hamiltonian annihilates the vacuum. -/
example (t V : Fin 2 → Fin 2 → ℂ) :
    (fermionGenericHamiltonian 1 t V).mulVec (fermionMultiVacuum 1) = 0 :=
  fermionGenericHamiltonian_mulVec_vacuum 1 t V

/-- The full Hubbard Hamiltonian annihilates the vacuum. -/
example (t : Fin 2 → Fin 2 → ℂ) (U : ℂ) :
    (hubbardHamiltonian 1 t U).mulVec (fermionMultiVacuum (2 * 1 + 1)) = 0 :=
  hubbardHamiltonian_mulVec_vacuum 1 t U

/-! ## Eigenstate construction (PRs #155-#157) -/

/-- Single-particle state `c_i† |vac⟩` has `N̂`-eigenvalue 1. -/
example (N : ℕ) (i : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i).mulVec (fermionMultiVacuum N)) =
      (fermionMultiCreation N i).mulVec (fermionMultiVacuum N) :=
  fermionTotalNumber_mulVec_singleParticle N i

/-- Two-particle state `c_i† c_j† |vac⟩` has `N̂`-eigenvalue 2. -/
example (N : ℕ) (i j : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N)) =
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N) :=
  fermionTotalNumber_mulVec_twoParticle N i j

/-- Generic charge-eigenstate helper: if `[N̂, X] = α X` and
`N̂ v = 0`, then `N̂ (X v) = α (X v)`. -/
example {N : ℕ} {X : ManyBodyOp (Fin (N + 1))} {α : ℂ}
    (hX : fermionTotalNumber N * X - X * fermionTotalNumber N = α • X)
    {v : (Fin (N + 1) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber N).mulVec v = 0) :
    (fermionTotalNumber N).mulVec (X.mulVec v) = α • X.mulVec v :=
  fermionTotalNumber_mulVec_eigenstate_of_commute hX hv

/-! ## Periodic Hubbard Gibbs state -/

/-- Periodic Hubbard Gibbs state Hermiticity. -/
example (N : ℕ) (β J U : ℝ) :
    (hubbardCycleGibbsState N β J U).IsHermitian :=
  hubbardCycleGibbsState_isHermitian N β J U

/-- Periodic Hubbard Gibbs state commutes with Hamiltonian. -/
example (N : ℕ) (β J U : ℝ) :
    Commute (hubbardCycleGibbsState N β J U) (hubbardCycleHamiltonian N J U) :=
  hubbardCycleGibbsState_commute_hamiltonian N β J U

end LatticeSystem.Tests.Hubbard
