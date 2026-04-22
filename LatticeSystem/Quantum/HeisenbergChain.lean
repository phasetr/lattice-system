/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.IsingChain
import LatticeSystem.Quantum.GibbsState
import LatticeSystem.Quantum.GibbsState.Covariance
import LatticeSystem.Quantum.MagnetizationSubspace
import LatticeSystem.Lattice.Graph

/-!
# One-dimensional Heisenberg chain coupling functions and Gibbs state

This module defines nearest-neighbour coupling functions for one-dimensional
spin chains with **open** and **periodic** boundary conditions. Combined
with the general `heisenbergHamiltonian J` from `SpinDot.lean`, these
yield the standard 1D Heisenberg Hamiltonians, and combined with the
abstract Gibbs framework from `GibbsState.lean`, the corresponding
finite-volume Gibbs states.

We prove:

* Hermiticity of the open-chain and periodic-chain Hamiltonians when the
  coupling constant `J` is real.
* Hermiticity, commutativity with `H`, and the high-temperature closed
  form for the corresponding Gibbs states.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
§3.3, p. 80 (Gibbs state stationarity); §3.5, p. 89 (Heisenberg chain).
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## Nearest-neighbour coupling functions -/

/-- Open-boundary nearest-neighbour coupling on `Fin (N + 1)`:
primary definition via `couplingOf (pathGraph (N+1)) (-J)`. The
negative sign encodes Tasaki's ferromagnetic convention
`H = -J Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y` (eq. (2.4.1)) so that `J > 0` is
ferromagnetic. -/
noncomputable def openChainCoupling (N : ℕ) (J : ℝ) :
    Fin (N + 1) → Fin (N + 1) → ℂ :=
  LatticeSystem.Lattice.couplingOf (SimpleGraph.pathGraph (N + 1)) (-(J : ℂ))

/-- Periodic nearest-neighbour coupling on `Fin (N + 2)` (at least 2 sites):
primary definition via `couplingOf (cycleGraph (N+2)) (-J)`. -/
noncomputable def periodicChainCoupling (N : ℕ) (J : ℝ) :
    Fin (N + 2) → Fin (N + 2) → ℂ :=
  LatticeSystem.Lattice.couplingOf (SimpleGraph.cycleGraph (N + 2)) (-(J : ℂ))

/-! ## Bridge to mathlib's `SimpleGraph.pathGraph` and `cycleGraph`

The standard 1D nearest-neighbour couplings are exactly the
`couplingOf` of the path / cycle graphs from
`LatticeSystem.Lattice.Graph`, with edge weight `-J` (Tasaki's
ferromagnetic sign convention). This makes explicit that our chain
Hamiltonians are instances of a general graph-defined Heisenberg
model in the sense of Miyao 2021 §3. -/

/-- The open-chain coupling equals `couplingOf (pathGraph (N+1)) (-J)`
definitionally (this is how it is now defined). -/
theorem openChainCoupling_eq_couplingOf (N : ℕ) (J : ℝ) :
    openChainCoupling N J =
      LatticeSystem.Lattice.couplingOf (SimpleGraph.pathGraph (N + 1))
        (-(J : ℂ)) :=
  rfl

/-- The periodic-chain coupling equals `couplingOf (cycleGraph (N+2)) (-J)`
definitionally. -/
theorem periodicChainCoupling_eq_couplingOf (N : ℕ) (J : ℝ) :
    periodicChainCoupling N J =
      LatticeSystem.Lattice.couplingOf (SimpleGraph.cycleGraph (N + 2))
        (-(J : ℂ)) :=
  rfl

/-- Explicit if-form for `openChainCoupling`: retained as an
unfolding lemma for existing downstream proofs that used
`simp [openChainCoupling_apply]` to reduce to the if-expression. -/
theorem openChainCoupling_apply (N : ℕ) (J : ℝ) (x y : Fin (N + 1)) :
    openChainCoupling N J x y
      = if x.val + 1 = y.val ∨ y.val + 1 = x.val then -(J : ℂ) else 0 := by
  unfold openChainCoupling LatticeSystem.Lattice.couplingOf
  by_cases h : (SimpleGraph.pathGraph (N + 1)).Adj x y
  · rw [if_pos h, SimpleGraph.pathGraph_adj] at *
    rw [if_pos h]
  · rw [SimpleGraph.pathGraph_adj] at h
    rw [if_neg (by rwa [SimpleGraph.pathGraph_adj]), if_neg h]

/-- Explicit if-form for `periodicChainCoupling`. -/
theorem periodicChainCoupling_apply (N : ℕ) (J : ℝ) (x y : Fin (N + 2)) :
    periodicChainCoupling N J x y
      = if x + 1 = y ∨ y + 1 = x then -(J : ℂ) else 0 := by
  unfold periodicChainCoupling LatticeSystem.Lattice.couplingOf
  by_cases h : (SimpleGraph.cycleGraph (N + 2)).Adj x y
  · rw [if_pos h,
      if_pos ((LatticeSystem.Lattice.cycleGraph_adj_iff N x y).mp h)]
  · rw [if_neg h, if_neg (fun h' => h
      ((LatticeSystem.Lattice.cycleGraph_adj_iff N x y).mpr h'))]

/-! ## Hermiticity -/

/-- A Heisenberg Hamiltonian with real symmetric coupling is Hermitian. -/
theorem heisenbergHamiltonian_isHermitian_of_real_symm
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {J : Λ → Λ → ℂ} (hreal : ∀ x y, star (J x y) = J x y)
    (hsymm : ∀ x y, J x y = J y x) :
    (heisenbergHamiltonian J).IsHermitian := by
  unfold heisenbergHamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  congr 1; funext x
  rw [Matrix.conjTranspose_sum]
  congr 1; funext y
  rw [Matrix.conjTranspose_smul, (spinHalfDot_isHermitian x y).eq]
  rw [hreal, hsymm, spinHalfDot_comm]

/-- Canonical named wrapper for the Heisenberg Hamiltonian with
hopping pattern derived from a `SimpleGraph G` and uniform complex
edge weight `J`. Parallel to `isingHamiltonianOnGraph`. -/
noncomputable def heisenbergHamiltonianOnGraph
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    ManyBodyOp Λ :=
  heisenbergHamiltonian (LatticeSystem.Lattice.couplingOf G J)

/-- **Heisenberg-on-graph Hermiticity.** For *any* `SimpleGraph G` on
the vertex set `Λ` and any real complex edge weight `J : ℂ` (i.e.
`star J = J`), the Heisenberg Hamiltonian
`heisenbergHamiltonian (couplingOf G J)` is Hermitian. The two
hypotheses required by
`heisenbergHamiltonian_isHermitian_of_real_symm` are exactly the
real and symmetric properties of `couplingOf G J` provided by
`couplingOf_real` and `couplingOf_symm` in
`LatticeSystem.Lattice.Graph`. -/
theorem heisenbergHamiltonian_couplingOf_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {J : ℂ}
    (hJ : star J = J) :
    (heisenbergHamiltonian
        (LatticeSystem.Lattice.couplingOf G J)).IsHermitian :=
  heisenbergHamiltonian_isHermitian_of_real_symm
    (LatticeSystem.Lattice.couplingOf_real G hJ)
    (LatticeSystem.Lattice.couplingOf_symm G J)

/-! ## Real-coupling identifications (Tasaki §2.3 input)

The chain / lattice coupling families above all take a *real*
parameter `J : ℝ` and produce complex couplings via `(-(J : ℂ))`,
which are entry-wise real. This is the key hypothesis required by
`timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec` to lift
to time-reversal invariance. -/

/-- Every entry of `openChainCoupling N J` is real (under complex
conjugation). -/
theorem openChainCoupling_conj (N : ℕ) (J : ℝ) (x y : Fin (N + 1)) :
    starRingEnd ℂ (openChainCoupling N J x y)
      = openChainCoupling N J x y := by
  apply LatticeSystem.Lattice.couplingOf_real
  show star (-(J : ℂ)) = -(J : ℂ)
  rw [star_neg]
  exact congrArg Neg.neg (Complex.conj_ofReal J)

/-- Every entry of `periodicChainCoupling N J` is real. -/
theorem periodicChainCoupling_conj
    (N : ℕ) (J : ℝ) (x y : Fin (N + 2)) :
    starRingEnd ℂ (periodicChainCoupling N J x y)
      = periodicChainCoupling N J x y := by
  apply LatticeSystem.Lattice.couplingOf_real
  show star (-(J : ℂ)) = -(J : ℂ)
  rw [star_neg]
  exact congrArg Neg.neg (Complex.conj_ofReal J)


/-! ## Heisenberg-on-graph SU(2) invariance

The existing generic-`J` SU(2)-invariance theorems for
`heisenbergHamiltonian` (proved in `Quantum/SpinDot.lean`)
specialise immediately to any graph-built coupling
`couplingOf G J`. We expose them under graph-centric names so that
downstream graph-defined Hamiltonians inherit the invariance
without any additional proof. -/

/-- For any graph `G` and edge weight `J : ℂ`, the Heisenberg
Hamiltonian on `G` commutes with `Ŝ_tot^(1)`. -/
theorem heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp1
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonian
        (LatticeSystem.Lattice.couplingOf G J)) (totalSpinHalfOp1 Λ) :=
  sub_eq_zero.mp
    (heisenbergHamiltonian_commutator_totalSpinHalfOp1
      (LatticeSystem.Lattice.couplingOf G J))

/-- For any graph `G` and edge weight `J : ℂ`, the Heisenberg
Hamiltonian on `G` commutes with `Ŝ_tot^(2)`. -/
theorem heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp2
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonian
        (LatticeSystem.Lattice.couplingOf G J)) (totalSpinHalfOp2 Λ) :=
  sub_eq_zero.mp
    (heisenbergHamiltonian_commutator_totalSpinHalfOp2
      (LatticeSystem.Lattice.couplingOf G J))

/-- For any graph `G` and edge weight `J : ℂ`, the Heisenberg
Hamiltonian on `G` commutes with `Ŝ_tot^(3)`. -/
theorem heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp3
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonian
        (LatticeSystem.Lattice.couplingOf G J)) (totalSpinHalfOp3 Λ) :=
  sub_eq_zero.mp
    (heisenbergHamiltonian_commutator_totalSpinHalfOp3
      (LatticeSystem.Lattice.couplingOf G J))

/-- For any graph `G` and edge weight `J : ℂ`, the Heisenberg
Hamiltonian on `G` commutes with the total-spin Casimir
`Ŝ_tot²`. -/
theorem heisenbergHamiltonian_couplingOf_commute_totalSpinHalfSquared
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonian
        (LatticeSystem.Lattice.couplingOf G J))
      (totalSpinHalfSquared Λ) :=
  heisenbergHamiltonian_commute_totalSpinHalfSquared _

/-! ### Named-wrapper corollaries -/

/-- Hermiticity of the graph-wrapper Hamiltonian for real `J`. -/
theorem heisenbergHamiltonianOnGraph_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {J : ℂ} (hJ : star J = J) :
    (heisenbergHamiltonianOnGraph G J).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian G hJ

/-- Commute with total-spin components. -/
theorem heisenbergHamiltonianOnGraph_commute_totalSpinHalfOp1
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonianOnGraph G J) (totalSpinHalfOp1 Λ) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp1 G J

theorem heisenbergHamiltonianOnGraph_commute_totalSpinHalfOp2
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonianOnGraph G J) (totalSpinHalfOp2 Λ) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp2 G J

theorem heisenbergHamiltonianOnGraph_commute_totalSpinHalfOp3
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonianOnGraph G J) (totalSpinHalfOp3 Λ) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp3 G J

theorem heisenbergHamiltonianOnGraph_commute_totalSpinHalfSquared
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergHamiltonianOnGraph G J) (totalSpinHalfSquared Λ) :=
  heisenbergHamiltonian_couplingOf_commute_totalSpinHalfSquared G J

/-! ## Heisenberg-on-graph Gibbs state

For any finite graph `G` with real edge weight `J : ℂ`, the Gibbs
state `ρ_β = gibbsState β (heisenbergHamiltonian (couplingOf G J))`
is defined and inherits Hermiticity from `gibbsState_isHermitian`
+ the graph-centric Hamiltonian Hermiticity (PR #140). This
prepares for thermal-state work on arbitrary finite graphs. -/

/-- The Heisenberg Gibbs state for a finite graph `G` with real
edge weight `J : ℂ` at inverse temperature `β : ℝ`. -/
noncomputable def heisenbergGibbsStateOnGraph
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    ManyBodyOp Λ :=
  gibbsState β (heisenbergHamiltonianOnGraph G J)

/-- The graph Heisenberg Gibbs state is Hermitian for any real
edge weight `J`. -/
theorem heisenbergGibbsStateOnGraph_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj] {J : ℂ}
    (hJ : star J = J) :
    (heisenbergGibbsStateOnGraph β G J).IsHermitian :=
  gibbsState_isHermitian
    (heisenbergHamiltonian_couplingOf_isHermitian G hJ) β

/-- The graph Heisenberg Gibbs state commutes with its Hamiltonian
(instance of the generic `gibbsState_commute_hamiltonian`). -/
theorem heisenbergGibbsStateOnGraph_commute_hamiltonian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) :
    Commute (heisenbergGibbsStateOnGraph β G J)
      (heisenbergHamiltonian (LatticeSystem.Lattice.couplingOf G J)) :=
  gibbsState_commute_hamiltonian β _

/-- The open-chain Heisenberg Hamiltonian is Hermitian. Now via
the graph-centric wrapper (`openChainCoupling` is definitionally
`couplingOf (pathGraph (N+1)) (-J)`). -/
theorem openChainHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-- The periodic-chain Heisenberg Hamiltonian is Hermitian. Via the
graph-centric wrapper (`periodicChainCoupling` is definitionally
`couplingOf (cycleGraph (N+2)) (-J)`). -/
theorem periodicChainHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (periodicChainCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-! ## Energy expectation as a bond-sum decomposition

Combining `gibbsExpectation_sum` (linearity over Finset sums) and
`gibbsExpectation_smul` (scalar pull-out) at the defining formula
`heisenbergHamiltonian J = ∑ x, ∑ y, J x y • spinHalfDot x y` gives an
explicit bond-sum decomposition of the energy expectation, valid for
any Gibbs Hamiltonian `H`. -/

/-- Generic bond-sum decomposition: for any Gibbs Hamiltonian `H` and
coupling `J`,
`⟨heisenbergHamiltonian J⟩_β = ∑ x, ∑ y, J x y · ⟨spinHalfDot x y⟩_β`. -/
theorem heisenbergHamiltonian_gibbsExpectation_eq
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (β : ℝ) (H : ManyBodyOp Λ) (J : Λ → Λ → ℂ) :
    gibbsExpectation β H (heisenbergHamiltonian J) =
      ∑ x : Λ, ∑ y : Λ, J x y * gibbsExpectation β H (spinHalfDot x y) := by
  unfold heisenbergHamiltonian
  rw [gibbsExpectation_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [gibbsExpectation_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  exact gibbsExpectation_smul β (J x y) (spinHalfDot x y)

/-- Open-chain Heisenberg energy as a bond-sum:
`⟨H_open⟩_β = ∑ x, ∑ y, openChainCoupling N J x y · ⟨Ŝ_x · Ŝ_y⟩_β`. -/
theorem openChainHeisenbergGibbsExpectation_self_eq (β J : ℝ) (N : ℕ) :
    gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        (heisenbergHamiltonian (openChainCoupling N J)) =
      ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        openChainCoupling N J x y *
          gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
            (spinHalfDot x y) :=
  heisenbergHamiltonian_gibbsExpectation_eq β
    (heisenbergHamiltonian (openChainCoupling N J)) (openChainCoupling N J)

/-- Periodic-chain Heisenberg energy as a bond-sum:
`⟨H_periodic⟩_β = ∑ x, ∑ y, periodicChainCoupling N J x y · ⟨Ŝ_x · Ŝ_y⟩_β`. -/
theorem periodicChainHeisenbergGibbsExpectation_self_eq (β J : ℝ) (N : ℕ) :
    gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        (heisenbergHamiltonian (periodicChainCoupling N J)) =
      ∑ x : Fin (N + 2), ∑ y : Fin (N + 2),
        periodicChainCoupling N J x y *
          gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
            (spinHalfDot x y) :=
  heisenbergHamiltonian_gibbsExpectation_eq β
    (heisenbergHamiltonian (periodicChainCoupling N J)) (periodicChainCoupling N J)

/-! ## Gibbs state for the open-chain Heisenberg Hamiltonian -/

/-- The Gibbs state of the open-boundary 1D Heisenberg chain on
`Fin (N + 1)` sites with real coupling `J` and inverse temperature `β`. -/
noncomputable def openChainHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 1)) :=
  gibbsState β (heisenbergHamiltonian (openChainCoupling N J))

/-- `openChainHeisenbergGibbsState` is definitionally equal to the
graph-form `heisenbergGibbsStateOnGraph` applied to `pathGraph (N+1)`. -/
theorem openChainHeisenbergGibbsState_eq_onGraph (β J : ℝ) (N : ℕ) :
    openChainHeisenbergGibbsState β J N
      = heisenbergGibbsStateOnGraph β (SimpleGraph.pathGraph (N + 1))
          (-(J : ℂ)) :=
  rfl

/-- The open-chain Heisenberg Gibbs state is Hermitian. -/
theorem openChainHeisenbergGibbsState_isHermitian (β J : ℝ) (N : ℕ) :
    (openChainHeisenbergGibbsState β J N).IsHermitian :=
  gibbsState_isHermitian (openChainHeisenberg_isHermitian N J) β

/-- The open-chain Heisenberg Gibbs state commutes with its Hamiltonian. -/
theorem openChainHeisenbergGibbsState_commute_hamiltonian (β J : ℝ) (N : ℕ) :
    Commute (openChainHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (openChainCoupling N J)) :=
  gibbsState_commute_hamiltonian β (heisenbergHamiltonian (openChainCoupling N J))

/-- Infinite-temperature (β = 0) closed form for the open-chain
Heisenberg expectation: `⟨A⟩_0 = (1/dim) · Tr A` for any observable `A`. -/
theorem openChainHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (openChainCoupling N J)) A
      = ((Fintype.card (Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (openChainCoupling N J)) A

/-- For any Hermitian observable `O`, the open-chain Heisenberg expectation
`⟨O⟩_β` is real (imaginary part vanishes). -/
theorem openChainHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J)) O).im = 0 :=
  gibbsExpectation_im_of_isHermitian (openChainHeisenberg_isHermitian N J) hO β

/-- Open-chain Heisenberg conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem openChainHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        (heisenbergHamiltonian (openChainCoupling N J) * A
          - A * heisenbergHamiltonian (openChainCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (openChainCoupling N J)) A

/-- Open-chain Heisenberg energy expectation is real:
`(⟨H_open⟩_β).im = 0`. -/
theorem openChainHeisenbergGibbsExpectation_hamiltonian_im (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        (heisenbergHamiltonian (openChainCoupling N J))).im = 0 :=
  gibbsExpectation_hamiltonian_im (openChainHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, the open-chain Heisenberg expectation
`⟨H_open · O⟩_β` is real. -/
theorem openChainHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        (heisenbergHamiltonian (openChainCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im (openChainHeisenberg_isHermitian N J) hO β

/-- Open-chain Heisenberg energy-squared expectation is real:
`(⟨H_open^2⟩_β).im = 0`. -/
theorem openChainHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        ((heisenbergHamiltonian (openChainCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (openChainHeisenberg_isHermitian N J) (openChainHeisenberg_isHermitian N J) β

/-- Open-chain Heisenberg energy n-th power expectation is real:
`(⟨H_open^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem openChainHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        ((heisenbergHamiltonian (openChainCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (openChainHeisenberg_isHermitian N J) (openChainHeisenberg_isHermitian N J) β n

/-- Open-chain Heisenberg anticommutator expectation is real:
for Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem openChainHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im (openChainHeisenberg_isHermitian N J) hA hB β

/-- Open-chain Heisenberg commutator expectation is purely imaginary:
for Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem openChainHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re (openChainHeisenberg_isHermitian N J) hA hB β

/-- Open-chain Heisenberg energy variance is real:
`(Var_β(H_open)).im = 0`. -/
theorem openChainHeisenbergGibbsHamiltonianVariance_im (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (openChainCoupling N J))
        (heisenbergHamiltonian (openChainCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (openChainHeisenberg_isHermitian N J) (openChainHeisenberg_isHermitian N J) β

/-- Open-chain Heisenberg partition function is real:
`(partitionFn β H_open).im = 0`. -/
theorem openChainHeisenberg_partitionFn_im (β J : ℝ) (N : ℕ) :
    (partitionFn β (heisenbergHamiltonian (openChainCoupling N J))).im = 0 :=
  partitionFn_im_of_isHermitian (openChainHeisenberg_isHermitian N J) β

/-- Open-chain Heisenberg expectation real-cast equality:
for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem openChainHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (((gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J)) O).re
        : ℂ))
      = gibbsExpectation β (heisenbergHamiltonian (openChainCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (openChainHeisenberg_isHermitian N J) hO β

/-- Open-chain Heisenberg Rényi-n trace identity:
`Tr(ρ_β^n) = Z(n β) / Z(β)^n`. -/
theorem openChainHeisenbergGibbsState_pow_trace (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((openChainHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (openChainCoupling N J))
        / (partitionFn β (heisenbergHamiltonian (openChainCoupling N J))) ^ n :=
  gibbsState_pow_trace β (heisenbergHamiltonian (openChainCoupling N J)) n

/-! ## Gibbs state for the periodic-chain Heisenberg Hamiltonian -/

/-- The Gibbs state of the periodic-boundary 1D Heisenberg chain on
`Fin (N + 2)` sites with real coupling `J` and inverse temperature `β`. -/
noncomputable def periodicChainHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 2)) :=
  gibbsState β (heisenbergHamiltonian (periodicChainCoupling N J))

/-- `periodicChainHeisenbergGibbsState` is definitionally equal to
the graph-form `heisenbergGibbsStateOnGraph` applied to
`cycleGraph (N+2)`. -/
theorem periodicChainHeisenbergGibbsState_eq_onGraph (β J : ℝ) (N : ℕ) :
    periodicChainHeisenbergGibbsState β J N
      = heisenbergGibbsStateOnGraph β (SimpleGraph.cycleGraph (N + 2))
          (-(J : ℂ)) :=
  rfl

/-- The periodic-chain Heisenberg Gibbs state is Hermitian. -/
theorem periodicChainHeisenbergGibbsState_isHermitian (β J : ℝ) (N : ℕ) :
    (periodicChainHeisenbergGibbsState β J N).IsHermitian :=
  gibbsState_isHermitian (periodicChainHeisenberg_isHermitian N J) β

/-- The periodic-chain Heisenberg Gibbs state commutes with its Hamiltonian. -/
theorem periodicChainHeisenbergGibbsState_commute_hamiltonian (β J : ℝ) (N : ℕ) :
    Commute (periodicChainHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (periodicChainCoupling N J)) :=
  gibbsState_commute_hamiltonian β
    (heisenbergHamiltonian (periodicChainCoupling N J))

/-- Infinite-temperature (β = 0) closed form for the periodic-chain
Heisenberg expectation: `⟨A⟩_0 = (1/dim) · Tr A` for any observable `A`. -/
theorem periodicChainHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 2))) :
    gibbsExpectation 0 (heisenbergHamiltonian (periodicChainCoupling N J)) A
      = ((Fintype.card (Fin (N + 2) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (periodicChainCoupling N J)) A

/-- For any Hermitian observable `O`, the periodic-chain Heisenberg
expectation `⟨O⟩_β` is real (imaginary part vanishes). -/
theorem periodicChainHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2))} (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J)) O).im = 0 :=
  gibbsExpectation_im_of_isHermitian (periodicChainHeisenberg_isHermitian N J) hO β

/-- Periodic-chain Heisenberg conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem periodicChainHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 2))) :
    gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        (heisenbergHamiltonian (periodicChainCoupling N J) * A
          - A * heisenbergHamiltonian (periodicChainCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (periodicChainCoupling N J)) A

/-- Periodic-chain Heisenberg energy expectation is real:
`(⟨H_periodic⟩_β).im = 0`. -/
theorem periodicChainHeisenbergGibbsExpectation_hamiltonian_im (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        (heisenbergHamiltonian (periodicChainCoupling N J))).im = 0 :=
  gibbsExpectation_hamiltonian_im (periodicChainHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, the periodic-chain Heisenberg expectation
`⟨H_periodic · O⟩_β` is real. -/
theorem periodicChainHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2))} (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        (heisenbergHamiltonian (periodicChainCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im (periodicChainHeisenberg_isHermitian N J) hO β

/-- Periodic-chain Heisenberg energy-squared expectation is real:
`(⟨H_periodic^2⟩_β).im = 0`. -/
theorem periodicChainHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        ((heisenbergHamiltonian (periodicChainCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (periodicChainHeisenberg_isHermitian N J)
    (periodicChainHeisenberg_isHermitian N J) β

/-- Periodic-chain Heisenberg energy n-th power expectation is real:
`(⟨H_periodic^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem periodicChainHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        ((heisenbergHamiltonian (periodicChainCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (periodicChainHeisenberg_isHermitian N J)
    (periodicChainHeisenberg_isHermitian N J) β n

/-- Periodic-chain Heisenberg anticommutator expectation is real:
for Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem periodicChainHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (periodicChainHeisenberg_isHermitian N J) hA hB β

/-- Periodic-chain Heisenberg commutator expectation is purely imaginary:
for Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem periodicChainHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (periodicChainCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (periodicChainHeisenberg_isHermitian N J) hA hB β

/-- Periodic-chain Heisenberg energy variance is real:
`(Var_β(H_periodic)).im = 0`. -/
theorem periodicChainHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (periodicChainCoupling N J))
        (heisenbergHamiltonian (periodicChainCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (periodicChainHeisenberg_isHermitian N J)
    (periodicChainHeisenberg_isHermitian N J) β

/-- Periodic-chain Heisenberg partition function is real:
`(partitionFn β H_periodic).im = 0`. -/
theorem periodicChainHeisenberg_partitionFn_im (β J : ℝ) (N : ℕ) :
    (partitionFn β (heisenbergHamiltonian (periodicChainCoupling N J))).im = 0 :=
  partitionFn_im_of_isHermitian (periodicChainHeisenberg_isHermitian N J) β

/-- Periodic-chain Heisenberg expectation real-cast equality:
for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem periodicChainHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2))} (hO : O.IsHermitian) :
    (((gibbsExpectation β
        (heisenbergHamiltonian (periodicChainCoupling N J)) O).re : ℂ))
      = gibbsExpectation β
          (heisenbergHamiltonian (periodicChainCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (periodicChainHeisenberg_isHermitian N J) hO β

/-- Periodic-chain Heisenberg Rényi-n trace identity:
`Tr(ρ_β^n) = Z(n β) / Z(β)^n`. -/
theorem periodicChainHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((periodicChainHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (periodicChainCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (periodicChainCoupling N J))) ^ n :=
  gibbsState_pow_trace β (heisenbergHamiltonian (periodicChainCoupling N J)) n

end LatticeSystem.Quantum
