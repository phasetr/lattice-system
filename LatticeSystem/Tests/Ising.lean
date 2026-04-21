/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.IsingChain

/-!
# Test coverage for Ising chain Gibbs state and expectation
theorems

Backfill regression tests for the chain Gibbs state and expectation
theorems in `Quantum/IsingChain.lean` (most merged before any test
infrastructure existed).
-/

namespace LatticeSystem.Tests.Ising

open LatticeSystem.Lattice LatticeSystem.Quantum SimpleGraph

/-! ## Chain Hamiltonian Hermiticity -/

/-- N=0 (single site, J ignored). -/
example (J h : ℝ) : (quantumIsingHamiltonian 0 J h).IsHermitian :=
  quantumIsingHamiltonian_isHermitian 0 J h

/-- N=2 (3-site chain). -/
example (J h : ℝ) : (quantumIsingHamiltonian 2 J h).IsHermitian :=
  quantumIsingHamiltonian_isHermitian 2 J h

/-! ## Gibbs state Hermiticity / commute -/

example (β J h : ℝ) (N : ℕ) :
    (quantumIsingGibbsState β J h N).IsHermitian :=
  quantumIsingGibbsState_isHermitian β J h N

example (β J h : ℝ) (N : ℕ) :
    Commute (quantumIsingGibbsState β J h N) (quantumIsingHamiltonian N J h) :=
  quantumIsingGibbsState_commute_hamiltonian β J h N

/-! ## Expectation properties -/

example (J h : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation 0 (quantumIsingHamiltonian N J h) A
      = ((Fintype.card (Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  quantumIsingGibbsExpectation_zero J h N A

example (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h) O).im = 0 :=
  quantumIsingGibbsExpectation_im_of_isHermitian β J h N hO

example (β J h : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h * A - A * quantumIsingHamiltonian N J h) = 0 :=
  quantumIsingGibbsExpectation_commutator_hamiltonian β J h N A

example (β J h : ℝ) (N : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h)).im = 0 :=
  quantumIsingGibbsExpectation_hamiltonian_im β J h N

example (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h * O)).im = 0 :=
  quantumIsingGibbsExpectation_mul_hamiltonian_im β J h N hO

example (β J h : ℝ) (N : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        ((quantumIsingHamiltonian N J h)^2)).im = 0 :=
  quantumIsingGibbsExpectation_hamiltonian_sq_im β J h N

example (β J h : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        ((quantumIsingHamiltonian N J h)^n)).im = 0 :=
  quantumIsingGibbsExpectation_hamiltonian_pow_im β J h N n

example (β J h : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (A * B + B * A)).im = 0 :=
  quantumIsingGibbsExpectation_anticommutator_im β J h N hA hB

example (β J h : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (A * B - B * A)).re = 0 :=
  quantumIsingGibbsExpectation_commutator_re β J h N hA hB

/-! ## Variance and partition function -/

example (β J h : ℝ) (N : ℕ) :
    (gibbsVariance β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h)).im = 0 :=
  quantumIsingGibbsHamiltonianVariance_im β J h N

example (β J h : ℝ) (N : ℕ) :
    (partitionFn β (quantumIsingHamiltonian N J h)).im = 0 :=
  quantumIsing_partitionFn_im β J h N

example (β J h : ℝ) (N : ℕ) (n : ℕ) :
    ((quantumIsingGibbsState β J h N)^n).trace
      = partitionFn ((n : ℝ) * β) (quantumIsingHamiltonian N J h)
        / (partitionFn β (quantumIsingHamiltonian N J h)) ^ n :=
  quantumIsingGibbsState_pow_trace β J h N n

/-! ## Ising-on-graph Gibbs state (PR #175) -/

example (β J h : ℝ) :
    (isingGibbsStateOnGraph (pathGraph 3) β J h).IsHermitian :=
  isingGibbsStateOnGraph_isHermitian _ β J h

example (β J h : ℝ) :
    Commute (isingGibbsStateOnGraph (pathGraph 3) β J h)
      (isingHamiltonianOnGraph (pathGraph 3) (J : ℂ) (h : ℂ)) :=
  isingGibbsStateOnGraph_commute_hamiltonian _ β J h

/-! ## Spin operator Hermiticity -/

example (N : ℕ) (i : Fin (N + 1)) : (spinZ N i).IsHermitian :=
  spinZ_isHermitian i

example (N : ℕ) (i : Fin (N + 1)) : (spinX N i).IsHermitian :=
  spinX_isHermitian i

end LatticeSystem.Tests.Ising
