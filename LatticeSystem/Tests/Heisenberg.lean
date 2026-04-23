/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.HeisenbergChain.Eigenvalues
import LatticeSystem.Quantum.HeisenbergChain.Gibbs
import LatticeSystem.Quantum.HeisenbergLattice
import LatticeSystem.Quantum.HeisenbergLattice.Companions

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

/-! ## 2D / 3D Heisenberg Gibbs states -/

/-- 2D open square-lattice Gibbs state Hermiticity. -/
example (β J : ℝ) (N : ℕ) :
    (squareLatticeHeisenbergGibbsState β J N).IsHermitian :=
  squareLatticeHeisenbergGibbsState_isHermitian β J N

/-- 2D open square-lattice Gibbs state commutes with H. -/
example (β J : ℝ) (N : ℕ) :
    Commute (squareLatticeHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (squareLatticeCoupling N J)) :=
  squareLatticeHeisenbergGibbsState_commute_hamiltonian β J N

/-- 2D torus Gibbs state Hermiticity. -/
example (β J : ℝ) (N : ℕ) :
    (squareTorusHeisenbergGibbsState β J N).IsHermitian :=
  squareTorusHeisenbergGibbsState_isHermitian β J N

/-- 2D torus Gibbs state commutes with H. -/
example (β J : ℝ) (N : ℕ) :
    Commute (squareTorusHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (squareTorusCoupling N J)) :=
  squareTorusHeisenbergGibbsState_commute_hamiltonian β J N

/-- 3D cubic-lattice Gibbs state Hermiticity. -/
example (β J : ℝ) (N : ℕ) :
    (cubicLatticeHeisenbergGibbsState β J N).IsHermitian :=
  cubicLatticeHeisenbergGibbsState_isHermitian β J N

/-- 3D cubic-lattice Gibbs state commutes with H. -/
example (β J : ℝ) (N : ℕ) :
    Commute (cubicLatticeHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (cubicLatticeCoupling N J)) :=
  cubicLatticeHeisenbergGibbsState_commute_hamiltonian β J N

/-! ## 2D / 3D Heisenberg full Gibbs companion family (PR #334 backfill)

Spot-checks for the 33 companion theorems backfilled in PR #334:
representative `_zero` (β=0 closed form), `_im_of_isHermitian`,
`_commutator_hamiltonian`, `_hamiltonian_pow_im`,
`_HamiltonianVariance_im`, and `_pow_trace` companions for each
of the three 2D / 3D Heisenberg variants. -/

/-- 2D square-lattice: β = 0 closed form `⟨A⟩_0 = (1/dim) · Tr A`. -/
example (J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1) × Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareLatticeCoupling N J)) A
      = ((Fintype.card (Fin (N + 1) × Fin (N + 1) → Fin 2) : ℂ))⁻¹
          * A.trace :=
  squareLatticeHeisenbergGibbsExpectation_zero J N A

/-- 2D torus: β = 0 closed form. -/
example (J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 2) × Fin (N + 2))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareTorusCoupling N J)) A
      = ((Fintype.card (Fin (N + 2) × Fin (N + 2) → Fin 2) : ℂ))⁻¹
          * A.trace :=
  squareTorusHeisenbergGibbsExpectation_zero J N A

/-- 3D cubic-lattice: β = 0 closed form. -/
example (J : ℝ) (N : ℕ)
    (A : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (cubicLatticeCoupling N J)) A
      = ((Fintype.card
            ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1) → Fin 2) : ℂ))⁻¹
          * A.trace :=
  cubicLatticeHeisenbergGibbsExpectation_zero J N A

/-- 2D square-lattice: `(⟨O⟩_β).im = 0` for Hermitian `O`. -/
example (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β
        (heisenbergHamiltonian (squareLatticeCoupling N J)) O).im = 0 :=
  squareLatticeHeisenbergGibbsExpectation_im_of_isHermitian β J N hO

/-- 2D square-lattice: `⟨[H, A]⟩_β = 0`. -/
example (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1) × Fin (N + 1))) :
    gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J) * A
          - A * heisenbergHamiltonian (squareLatticeCoupling N J)) = 0 :=
  squareLatticeHeisenbergGibbsExpectation_commutator_hamiltonian β J N A

/-- 2D square-lattice: `(⟨H^n⟩_β).im = 0`. -/
example (β J : ℝ) (N n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        ((heisenbergHamiltonian (squareLatticeCoupling N J)) ^ n)).im = 0 :=
  squareLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im β J N n

/-- 2D square-lattice: energy variance is real. -/
example (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J))).im = 0 :=
  squareLatticeHeisenbergGibbsHamiltonianVariance_im β J N

/-- 2D torus: `(⟨H^n⟩_β).im = 0`. -/
example (β J : ℝ) (N n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        ((heisenbergHamiltonian (squareTorusCoupling N J)) ^ n)).im = 0 :=
  squareTorusHeisenbergGibbsExpectation_hamiltonian_pow_im β J N n

/-- 2D torus: anticommutator expectation real. -/
example (β J : ℝ) (N : ℕ)
    {A B : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (A * B + B * A)).im = 0 :=
  squareTorusHeisenbergGibbsExpectation_anticommutator_im β J N hA hB

/-- 3D cubic-lattice: `(⟨H^n⟩_β).im = 0`. -/
example (β J : ℝ) (N n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        ((heisenbergHamiltonian (cubicLatticeCoupling N J)) ^ n)).im = 0 :=
  cubicLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im β J N n

/-- 3D cubic-lattice: commutator expectation purely imaginary. -/
example (β J : ℝ) (N : ℕ)
    {A B : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (A * B - B * A)).re = 0 :=
  cubicLatticeHeisenbergGibbsExpectation_commutator_re β J N hA hB

/-- 3D cubic-lattice: Rényi-n trace identity. -/
example (β J : ℝ) (N n : ℕ) :
    ((cubicLatticeHeisenbergGibbsState β J N) ^ n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (cubicLatticeCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (cubicLatticeCoupling N J))) ^ n :=
  cubicLatticeHeisenbergGibbsState_pow_trace β J N n

/-! ## A. decide-based universal: graph adjacency on small `Fin n`
(Phase 1 PR 4 strengthening, refactor plan v4 §2.1 method A) -/

/-- `pathGraph 3` adjacency is symmetric (universally on `Fin 3`). -/
example : ∀ x y : Fin 3, (pathGraph 3).Adj x y = (pathGraph 3).Adj y x := by
  decide

/-- `pathGraph 3` adjacency is irreflexive. -/
example : ∀ x : Fin 3, ¬ (pathGraph 3).Adj x x := by decide

/-- `cycleGraph 4` adjacency is symmetric. -/
example : ∀ x y : Fin 4, (cycleGraph 4).Adj x y = (cycleGraph 4).Adj y x := by
  decide

/-- `pathGraph 3` has 4 ordered adjacent pairs (= 2 undirected edges). -/
example :
    (Finset.univ.filter
        (fun p : Fin 3 × Fin 3 => (pathGraph 3).Adj p.1 p.2)).card = 4 := by
  decide

/-- `cycleGraph 4` has 8 ordered adjacent pairs (= 4 undirected edges). -/
example :
    (Finset.univ.filter
        (fun p : Fin 4 × Fin 4 => (cycleGraph 4).Adj p.1 p.2)).card = 8 := by
  decide

/-! ## C. bridge identity: chain coupling = couplingOf (Phase 1 PR 4
strengthening, refactor plan v4 §2.1 method C) -/

/-- `openChainCoupling N J = couplingOf (pathGraph (N+1)) (-J)`
holds definitionally. Bridge between chain-specific and graph-centric
APIs. -/
example (N : ℕ) (J : ℝ) :
    openChainCoupling N J =
      couplingOf (pathGraph (N + 1)) (-(J : ℂ)) := rfl

/-- `periodicChainCoupling N J = couplingOf (cycleGraph (N+2)) (-J)`
holds definitionally. -/
example (N : ℕ) (J : ℝ) :
    periodicChainCoupling N J =
      couplingOf (cycleGraph (N + 2)) (-(J : ℂ)) := rfl

/-! ## G. small exhaustive: `couplingOf` values on `Fin 2 × Fin 2`
(Phase 1 PR 4 strengthening, refactor plan v4 §2.1 method G) -/

/-- The 2-site path-graph coupling on `Fin 2 × Fin 2` follows the
adjacency exactly. -/
example (J : ℝ) :
    ∀ x y : Fin 2,
        couplingOf (pathGraph 2) (-(J : ℂ)) x y =
          (if (pathGraph 2).Adj x y then -(J : ℂ) else 0) := by
  intro x y
  rfl

/-! ## D. HeisenbergChain extension coverage (codex audit Item 7)

Direct spot-checks for `HeisenbergChain/Eigenvalues.lean` and
`HeisenbergChain/Gibbs.lean`. Was previously covered only
indirectly through 2D / 3D wrappers and bond-action lemmas. -/

/-- 2-site explicit form: `H_open(N=1, J) = -2J · Ŝ_0 · Ŝ_1`. -/
example (J : ℝ) :
    heisenbergHamiltonian (openChainCoupling 1 J) =
      (-(2 * J) : ℂ) • spinHalfDot (0 : Fin 2) 1 :=
  openChainHeisenbergHamiltonian_two_site_eq J

/-- 3-site explicit form: `H_open(N=2, J) = -2J (Ŝ_0·Ŝ_1 + Ŝ_1·Ŝ_2)`. -/
example (J : ℝ) :
    heisenbergHamiltonian (openChainCoupling 2 J) =
      (-(2 * J) : ℂ) • (spinHalfDot (0 : Fin 3) 1 + spinHalfDot 1 2) :=
  openChainHeisenbergHamiltonian_three_site_eq J

/-- The open chain Heisenberg Hamiltonian preserves every
magnetisation sector `H_M`. -/
example (N : ℕ) (J : ℝ) {M : ℂ} {v : (Fin (N + 1) → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace (Fin (N + 1)) M) :
    (heisenbergHamiltonian (openChainCoupling N J)).mulVec v ∈
      magnetizationSubspace (Fin (N + 1)) M :=
  openChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem N J hv

/-- The periodic chain Heisenberg Hamiltonian preserves every
magnetisation sector. -/
example (N : ℕ) (J : ℝ) {M : ℂ} {v : (Fin (N + 2) → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace (Fin (N + 2)) M) :
    (heisenbergHamiltonian (periodicChainCoupling N J)).mulVec v ∈
      magnetizationSubspace (Fin (N + 2)) M :=
  periodicChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem N J hv

/-- 1D open-chain Heisenberg: β = 0 closed form. -/
example (J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (openChainCoupling N J)) A
      = ((Fintype.card (Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  openChainHeisenbergGibbsExpectation_zero J N A

/-- 1D open-chain Heisenberg: `(⟨H^n⟩_β).im = 0`. -/
example (β J : ℝ) (N n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        ((heisenbergHamiltonian (openChainCoupling N J)) ^ n)).im = 0 :=
  openChainHeisenbergGibbsExpectation_hamiltonian_pow_im β J N n

/-- 1D periodic-chain Heisenberg: `(⟨H^n⟩_β).im = 0`. -/
example (β J : ℝ) (N n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        ((heisenbergHamiltonian (periodicChainCoupling N J)) ^ n)).im = 0 :=
  periodicChainHeisenbergGibbsExpectation_hamiltonian_pow_im β J N n

end LatticeSystem.Tests.Heisenberg
