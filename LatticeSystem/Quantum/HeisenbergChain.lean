/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.IsingChain
import LatticeSystem.Quantum.GibbsState

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
`J(x, y) = J` if `|x - y| = 1`, else `0`. -/
noncomputable def openChainCoupling (N : ℕ) (J : ℝ) : Fin (N + 1) → Fin (N + 1) → ℂ :=
  fun x y => if (x.val + 1 = y.val) ∨ (y.val + 1 = x.val) then -(J : ℂ) else 0

/-- Periodic nearest-neighbour coupling on `Fin (N + 2)` (at least 2 sites):
`J(x, y) = -J` if `y ≡ x + 1 (mod N+2)` or vice versa, else `0`. -/
noncomputable def periodicChainCoupling (N : ℕ) (J : ℝ) :
    Fin (N + 2) → Fin (N + 2) → ℂ :=
  fun x y => if (x + 1 = y) ∨ (y + 1 = x) then -(J : ℂ) else 0

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

/-- The open-chain Heisenberg Hamiltonian is Hermitian. -/
theorem openChainHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_isHermitian_of_real_symm
    (by intro x y; simp [openChainCoupling]; split_ifs <;> simp)
    (by intro x y; simp [openChainCoupling, or_comm])

/-- The periodic-chain Heisenberg Hamiltonian is Hermitian. -/
theorem periodicChainHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (periodicChainCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_isHermitian_of_real_symm
    (by intro x y; simp only [periodicChainCoupling]; split_ifs <;> simp)
    (by intro x y; simp only [periodicChainCoupling]; simp [or_comm])

/-! ## Gibbs state for the open-chain Heisenberg Hamiltonian -/

/-- The Gibbs state of the open-boundary 1D Heisenberg chain on
`Fin (N + 1)` sites with real coupling `J` and inverse temperature `β`. -/
noncomputable def openChainHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 1)) :=
  gibbsState β (heisenbergHamiltonian (openChainCoupling N J))

/-- The open-chain Heisenberg Gibbs state is Hermitian. -/
theorem openChainHeisenbergGibbsState_isHermitian (β J : ℝ) (N : ℕ) :
    (openChainHeisenbergGibbsState β J N).IsHermitian :=
  gibbsState_isHermitian (openChainHeisenberg_isHermitian N J) β

/-- The open-chain Heisenberg Gibbs state commutes with its Hamiltonian. -/
theorem openChainHeisenbergGibbsState_commute_hamiltonian (β J : ℝ) (N : ℕ) :
    Commute (openChainHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (openChainCoupling N J)) :=
  gibbsState_commute_hamiltonian β (heisenbergHamiltonian (openChainCoupling N J))

/-- High-temperature closed form for the open-chain Heisenberg expectation:
`⟨A⟩_0 = (1/dim) · Tr A` for any observable `A`. -/
theorem openChainHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (openChainCoupling N J)) A
      = ((Fintype.card (Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (openChainCoupling N J)) A

/-! ## Gibbs state for the periodic-chain Heisenberg Hamiltonian -/

/-- The Gibbs state of the periodic-boundary 1D Heisenberg chain on
`Fin (N + 2)` sites with real coupling `J` and inverse temperature `β`. -/
noncomputable def periodicChainHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 2)) :=
  gibbsState β (heisenbergHamiltonian (periodicChainCoupling N J))

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

/-- High-temperature closed form for the periodic-chain Heisenberg expectation:
`⟨A⟩_0 = (1/dim) · Tr A` for any observable `A`. -/
theorem periodicChainHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 2))) :
    gibbsExpectation 0 (heisenbergHamiltonian (periodicChainCoupling N J)) A
      = ((Fintype.card (Fin (N + 2) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (periodicChainCoupling N J)) A

end LatticeSystem.Quantum
