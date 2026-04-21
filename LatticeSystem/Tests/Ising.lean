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

/-! ## Computational matrix-entry tests (attempted, partially blocked)

Per codex consultation (see `.self-local/docs/ising-bridge-plan.md`)
the plan was to add matrix-entry tests at the 2-site (N=1) level
to catch any behavioural drift in the
`quantumIsingHamiltonian` → `isingHamiltonianGeneric` bridge.

The computational entry-level tests turned out to be blocked: the
many-body matrix expression after unfolding
`onSite` + `pauliX/Z` + multi-site product is too complex for
`simp` to reduce in a stable way. Instead, the bridge theorem
itself (PR #187) serves as the primary regression test:
its proof fixes the normalisation.

Alternative robust tests (still TODO):
- `mulVec` on `basisVec`: cleanly reduces via
  `onSite_mulVec_basisVec`. E.g.
  `H.mulVec (basisVec all-up) = (-J) • basisVec all-up` when h=0.
- Bridge identity by `unfold; simp_rw; funext; ...` comparing
  operator-level equality rather than entry-level equality. -/

/-! ## Ising bridge theorem specialisations (PR #187)

The generic bridge
`quantumIsingHamiltonian N J h
  = isingHamiltonianGeneric (couplingOf (pathGraph (N+1)) (-J/2)) h`
instantiated at small `N`, as shim regression tests alongside
the generic proof. -/

example (J h : ℝ) :
    quantumIsingHamiltonian 0 J h
      = isingHamiltonianGeneric
          (couplingOf (SimpleGraph.pathGraph 1) (-(J : ℂ) / 2))
          (h : ℂ) :=
  quantumIsingHamiltonian_eq_isingHamiltonianGeneric 0 J h

example (J h : ℝ) :
    quantumIsingHamiltonian 2 J h
      = isingHamiltonianGeneric
          (couplingOf (SimpleGraph.pathGraph 3) (-(J : ℂ) / 2))
          (h : ℂ) :=
  quantumIsingHamiltonian_eq_isingHamiltonianGeneric 2 J h

example (J h : ℝ) :
    quantumIsingHamiltonian 3 J h
      = isingHamiltonianGeneric
          (couplingOf (SimpleGraph.pathGraph 4) (-(J : ℂ) / 2))
          (h : ℂ) :=
  quantumIsingHamiltonian_eq_isingHamiltonianGeneric 3 J h

/-! ## sum_pathGraph_{forward,backward,adj} helpers (PR #187)

Concrete small-N instances of the edge-sum decomposition. -/

example (f : Fin 3 → Fin 3 → ℕ) :
    ∑ x : Fin 3, ∑ y : Fin 3,
      (if x.val + 1 = y.val then f x y else 0)
    = ∑ i : Fin 2, f i.castSucc i.succ :=
  LatticeSystem.Lattice.sum_pathGraph_forward 2 f

example (f : Fin 4 → Fin 4 → ℕ) :
    ∑ x : Fin 4, ∑ y : Fin 4,
      (if y.val + 1 = x.val then f x y else 0)
    = ∑ i : Fin 3, f i.succ i.castSucc :=
  LatticeSystem.Lattice.sum_pathGraph_backward 3 f

example (f : Fin 3 → Fin 3 → ℕ) :
    ∑ x : Fin 3, ∑ y : Fin 3,
      (if (SimpleGraph.pathGraph 3).Adj x y then f x y else 0)
    = ∑ i : Fin 2, (f i.castSucc i.succ + f i.succ i.castSucc) :=
  LatticeSystem.Lattice.sum_pathGraph_adj 2 f

/-! ## Periodic Ising chain Gibbs state -/

/-- Periodic Ising Gibbs state Hermiticity. -/
example (N : ℕ) (β J h : ℝ) :
    (isingCycleGibbsState N β J h).IsHermitian :=
  isingCycleGibbsState_isHermitian N β J h

/-- Periodic Ising Gibbs state commutes with Hamiltonian. -/
example (N : ℕ) (β J h : ℝ) :
    Commute (isingCycleGibbsState N β J h) (isingCycleHamiltonian N J h) :=
  isingCycleGibbsState_commute_hamiltonian N β J h

end LatticeSystem.Tests.Ising
