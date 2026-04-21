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

/-! ## Computational matrix-entry tests (pre-bridge regression guards)

These tests pin down the value of `quantumIsingHamiltonian` at
specific matrix entries on the 2-site (N=1) chain. They are
**robust to internal refactors** — if the upcoming bridge to
`isingHamiltonianGeneric (couplingOf (pathGraph 2) (-J/2)) h`
preserves behaviour, these values stay fixed; if it accidentally
changes normalization (e.g. a missing factor of 2), the tests
fail loudly.

See `.self-local/docs/ising-bridge-plan.md` for the codex
consultation and rationale. -/

/-- Diagonal entry on the all-up state: `⟨↑↑|H|↑↑⟩ = -J` for the
2-site chain (edge count = 1). The ZZ bond gives σ^z_0 σ^z_1 · 1
= 1 on up-up; the X term is off-diagonal so contributes 0 here. -/
example (J : ℝ) :
    (quantumIsingHamiltonian 1 J 0)
        (fun _ : Fin 2 => (0 : Fin 2))
        (fun _ : Fin 2 => (0 : Fin 2))
      = -(J : ℂ) := by
  unfold quantumIsingHamiltonian spinZ spinX onSite pauliX pauliZ
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_succ]

/-- Same but with general real `h`: the ZZ term still gives `-J`
on the diagonal (since σ^x is purely off-diagonal and doesn't
contribute to diag). -/
example (J h : ℝ) :
    (quantumIsingHamiltonian 1 J h)
        (fun _ : Fin 2 => (0 : Fin 2))
        (fun _ : Fin 2 => (0 : Fin 2))
      = -(J : ℂ) := by
  unfold quantumIsingHamiltonian spinZ spinX onSite pauliX pauliZ
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_succ]

/-- Off-diagonal, site-0 flipped: `⟨↓↑|H|↑↑⟩ = -h`. The ZZ term
contributes 0 (σ^z is diagonal, so ⟨↓↑|σ^z_0 σ^z_1|↑↑⟩ has the
wrong site-0 matrix element); the X term contributes `-h` via
σ^x_0 flipping site 0. -/
example (J h : ℝ) :
    (quantumIsingHamiltonian 1 J h)
        (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 0 1)
        (fun _ : Fin 2 => (0 : Fin 2))
      = -(h : ℂ) := by
  unfold quantumIsingHamiltonian spinZ spinX onSite pauliX pauliZ
  simp [Matrix.add_apply, Fin.sum_univ_succ]

/-- Off-diagonal, site-1 flipped: `⟨↑↓|H|↑↑⟩ = -h` (symmetric to
above). -/
example (J h : ℝ) :
    (quantumIsingHamiltonian 1 J h)
        (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 1 1)
        (fun _ : Fin 2 => (0 : Fin 2))
      = -(h : ℂ) := by
  unfold quantumIsingHamiltonian spinZ spinX onSite pauliX pauliZ
  simp [Matrix.add_apply, Fin.sum_univ_succ]

/-- Two-flip off-diagonal: `⟨↓↓|H|↑↑⟩ = 0` (σ^x is single-site,
cannot flip two sites simultaneously; σ^z is diagonal). -/
example (J h : ℝ) :
    (quantumIsingHamiltonian 1 J h)
        (fun _ : Fin 2 => (1 : Fin 2))
        (fun _ : Fin 2 => (0 : Fin 2))
      = 0 := by
  unfold quantumIsingHamiltonian spinZ spinX onSite pauliX pauliZ
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_succ]

end LatticeSystem.Tests.Ising
