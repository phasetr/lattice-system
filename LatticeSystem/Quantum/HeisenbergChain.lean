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

end LatticeSystem.Quantum
