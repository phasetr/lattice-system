/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.IsingChain

/-!
# One-dimensional Heisenberg chain coupling functions

This module defines nearest-neighbour coupling functions for one-dimensional
spin chains with **open** and **periodic** boundary conditions. Combined
with the general `heisenbergHamiltonian J` from `SpinDot.lean`, these
yield the standard 1D Heisenberg Hamiltonians.

We also prove Hermiticity of the resulting Hamiltonians when the coupling
constant `J` is real.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
§3.5, p. 89.
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

end LatticeSystem.Quantum
