/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.HeisenbergChain

/-!
# Test coverage for Heisenberg-on-graph infrastructure

Backfill regression tests for PRs #138, #140, #141, #145, #146,
#149, #150 (Heisenberg-on-graph framework + concrete instances).
-/

namespace LatticeSystem.Tests.Heisenberg

open LatticeSystem.Lattice LatticeSystem.Quantum SimpleGraph

/-! ## Heisenberg-on-graph Hermiticity (PR #140) -/

/-- Hermiticity on `pathGraph 3` for real edge weight. -/
example (J : ℝ) :
    (heisenbergHamiltonian
        (couplingOf (pathGraph 3) (-(J : ℂ)))).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-- Hermiticity on `cycleGraph 4` for real edge weight. -/
example (J : ℝ) :
    (heisenbergHamiltonian
        (couplingOf (cycleGraph 4) (-(J : ℂ)))).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-- Hermiticity on a 2×2 product graph (open square). -/
example (J : ℝ) :
    (heisenbergHamiltonian
        (couplingOf (pathGraph 2 □ pathGraph 2)
          (-(J : ℂ)))).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-! ## SU(2) invariance corollaries (PR #145) -/

/-- Commute with `Ŝ_tot^{(1)}` on `pathGraph 3`. -/
example (J : ℂ) :
    Commute (heisenbergHamiltonian
        (couplingOf (pathGraph 3) J))
      (totalSpinHalfOp1 (Fin 3)) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp1 _ J

/-- Commute with `Ŝ_tot^{(2)}` on `cycleGraph 4`. -/
example (J : ℂ) :
    Commute (heisenbergHamiltonian
        (couplingOf (cycleGraph 4) J))
      (totalSpinHalfOp2 (Fin 4)) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp2 _ J

/-- Commute with `Ŝ_tot^{(3)}` on `pathGraph 4`. -/
example (J : ℂ) :
    Commute (heisenbergHamiltonian
        (couplingOf (pathGraph 4) J))
      (totalSpinHalfOp3 (Fin 4)) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp3 _ J

/-- Commute with the Casimir `Ŝ_tot²` on `cycleGraph 3`. -/
example (J : ℂ) :
    Commute (heisenbergHamiltonian
        (couplingOf (cycleGraph 3) J))
      (totalSpinHalfSquared (Fin 3)) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfSquared _ J

/-! ## Heisenberg-on-graph Gibbs state (PR #146) -/

/-- The 3-site Heisenberg-on-graph Gibbs state on `pathGraph 3` is
Hermitian for real edge weight. -/
example (β : ℝ) (J : ℝ) :
    (heisenbergGibbsStateOnGraph β (pathGraph 3)
        (-(J : ℂ))).IsHermitian :=
  heisenbergGibbsStateOnGraph_isHermitian β _ (by simp)

/-- The Gibbs state commutes with the corresponding Hamiltonian. -/
example (β : ℝ) (J : ℂ) :
    Commute (heisenbergGibbsStateOnGraph β (pathGraph 3) J)
      (heisenbergHamiltonian
        (couplingOf (pathGraph 3) J)) :=
  heisenbergGibbsStateOnGraph_commute_hamiltonian β _ J

/-! ## Concrete chain / lattice Hermiticity instances (PRs #141, #149, #150) -/

/-- 2-site open Heisenberg chain Hermiticity. -/
example (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).IsHermitian :=
  openChainHeisenberg_isHermitian 1 J

/-- 3-site periodic Heisenberg chain Hermiticity. -/
example (J : ℝ) :
    (heisenbergHamiltonian (periodicChainCoupling 1 J)).IsHermitian :=
  periodicChainHeisenberg_isHermitian 1 J

/-- 2D 2×2 open square lattice Heisenberg Hermiticity (PR #141). -/
example (J : ℝ) :
    (heisenbergHamiltonian (squareLatticeCoupling 1 J)).IsHermitian :=
  squareLatticeHeisenberg_isHermitian 1 J

/-- 2D 3×3 open square lattice Heisenberg Hermiticity. -/
example (J : ℝ) :
    (heisenbergHamiltonian (squareLatticeCoupling 2 J)).IsHermitian :=
  squareLatticeHeisenberg_isHermitian 2 J

/-- 2D 3×3 periodic torus Heisenberg Hermiticity (PR #149). -/
example (J : ℝ) :
    (heisenbergHamiltonian (squareTorusCoupling 1 J)).IsHermitian :=
  squareTorusHeisenberg_isHermitian 1 J

/-- 3D 2×2×2 open cubic lattice Heisenberg Hermiticity (PR #150). -/
example (J : ℝ) :
    (heisenbergHamiltonian (cubicLatticeCoupling 1 J)).IsHermitian :=
  cubicLatticeHeisenberg_isHermitian 1 J

/-! ## Heisenberg-on-graph named wrapper (PR #189) -/

example (J : ℝ) :
    (heisenbergHamiltonianOnGraph (pathGraph 3)
        (-(J : ℂ))).IsHermitian :=
  heisenbergHamiltonianOnGraph_isHermitian _ (by simp)

example (J : ℂ) :
    Commute (heisenbergHamiltonianOnGraph (cycleGraph 4) J)
      (totalSpinHalfOp1 (Fin 4)) :=
  heisenbergHamiltonianOnGraph_commute_totalSpinHalfOp1 _ J

example (J : ℂ) :
    Commute (heisenbergHamiltonianOnGraph (pathGraph 3) J)
      (totalSpinHalfSquared (Fin 3)) :=
  heisenbergHamiltonianOnGraph_commute_totalSpinHalfSquared _ J

end LatticeSystem.Tests.Heisenberg
