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
`J(x, y) = -J` if `|x.val - y.val| = 1`, else `0`. The negative sign
encodes Tasaki's ferromagnetic convention `H = -J Σ_{⟨x,y⟩} Ŝ_x · Ŝ_y`
(eq. (2.4.1)) so that `J > 0` is ferromagnetic. -/
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

/-! ## 2-site (Fin 2) explicit form and spectrum (Tasaki §2.4)

The simplest concrete instance: for `N = 1` (the open chain on `Fin 2`),
the Heisenberg Hamiltonian collapses to a single bond term. The four
distinguished states (all-up, all-down, singlet, triplet `m=0`) are
exact eigenstates with eigenvalues `-J/2, -J/2, +3J/2, -J/2`. -/

/-- Explicit form of the 2-site open chain Heisenberg Hamiltonian:
`H_open(N=1) = -2J · spinHalfDot 0 1`. -/
theorem openChainHeisenbergHamiltonian_two_site_eq (J : ℝ) :
    heisenbergHamiltonian (openChainCoupling 1 J) =
      (-(2 * J) : ℂ) • spinHalfDot (0 : Fin 2) 1 := by
  unfold heisenbergHamiltonian
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  -- Compute openChainCoupling 1 J for each of the 4 (x,y) pairs.
  have h00 : openChainCoupling 1 J 0 0 = 0 := by
    simp [openChainCoupling]
  have h01 : openChainCoupling 1 J 0 1 = -(J : ℂ) := by
    simp [openChainCoupling]
  have h10 : openChainCoupling 1 J 1 0 = -(J : ℂ) := by
    simp [openChainCoupling]
  have h11 : openChainCoupling 1 J 1 1 = 0 := by
    simp [openChainCoupling]
  rw [h00, h01, h10, h11]
  -- spinHalfDot 1 0 = spinHalfDot 0 1 by symmetry; combine the two -J terms.
  rw [spinHalfDot_comm 1 0]
  rw [zero_smul, zero_smul, zero_add, add_zero]
  rw [show (-(J : ℂ)) • spinHalfDot (0 : Fin 2) 1 + -(J : ℂ) • spinHalfDot 0 1 =
        (-(2 * J : ℂ)) • spinHalfDot 0 1 from by
    rw [← add_smul]; ring_nf]

/-- Eigenvalue on the all-up state for the 2-site open chain Heisenberg
Hamiltonian: `H · |↑↑⟩ = -(J/2) · |↑↑⟩`. This is the explicit
ferromagnetic ground-state energy `-S²·|B|·1` for `S = 1/2`, `|B| = 1`. -/
theorem openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_all_up (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (basisVec (fun _ : Fin 2 => (0 : Fin 2))) =
      (-(J / 2 : ℂ)) • basisVec (fun _ : Fin 2 => (0 : Fin 2)) := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  -- spinHalfDot 0 1 |↑↑⟩ = (1/4) |↑↑⟩ for x ≠ y
  have h : (spinHalfDot (0 : Fin 2) 1).mulVec
      (basisVec (fun _ : Fin 2 => (0 : Fin 2))) =
        (1 / 4 : ℂ) • basisVec (fun _ : Fin 2 => (0 : Fin 2)) :=
    spinHalfDot_mulVec_basisVec_both_up (by decide)
  rw [h, smul_smul]
  congr 1; ring

/-- Eigenvalue on the singlet for the 2-site open chain Heisenberg
Hamiltonian: `H · (|↑↓⟩ - |↓↑⟩) = (3J/2) · (|↑↓⟩ - |↓↑⟩)`. The
singlet is the exact ground state for antiferromagnetic `J > 0`
(Tasaki §2.5 conventions). -/
theorem openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_singlet (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (basisVec upDown - basisVec (basisSwap upDown 0 1)) =
      ((3 * J / 2 : ℂ)) • (basisVec upDown - basisVec (basisSwap upDown 0 1)) := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  have h := spinHalfDot_mulVec_singlet (Λ := Fin 2) (x := 0) (y := 1) (by decide)
    upDown upDown_antiparallel
  rw [h, smul_smul]
  congr 1; ring

/-- Eigenvalue on the all-down state for the 2-site open chain
Heisenberg Hamiltonian: `H · |↓↓⟩ = -(J/2) · |↓↓⟩`. By the SU(2)
symmetry, the all-down state has the same eigenvalue as the all-up
state (both lie in the `S = 1` triplet representation). -/
theorem openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_all_down (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (basisVec (fun _ : Fin 2 => (1 : Fin 2))) =
      (-(J / 2 : ℂ)) • basisVec (fun _ : Fin 2 => (1 : Fin 2)) := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  have h : (spinHalfDot (0 : Fin 2) 1).mulVec
      (basisVec (fun _ : Fin 2 => (1 : Fin 2))) =
        (1 / 4 : ℂ) • basisVec (fun _ : Fin 2 => (1 : Fin 2)) :=
    spinHalfDot_mulVec_basisVec_both_down (by decide)
  rw [h, smul_smul]
  congr 1; ring

/-- Eigenvalue on the triplet `m = 0` state for the 2-site open chain
Heisenberg Hamiltonian: `H · (|↑↓⟩ + |↓↑⟩) = -(J/2) · (|↑↓⟩ + |↓↑⟩)`.
The triplet representation `S = 1` has 3 degenerate states
(`|↑↑⟩, |↓↓⟩, |↑↓⟩+|↓↑⟩`) all with eigenvalue `-J/2`. -/
theorem openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_triplet_zero (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (basisVec upDown + basisVec (basisSwap upDown 0 1)) =
      (-(J / 2 : ℂ)) • (basisVec upDown + basisVec (basisSwap upDown 0 1)) := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  have h := spinHalfDot_mulVec_triplet_anti (Λ := Fin 2) (x := 0) (y := 1)
    (by decide) upDown upDown_antiparallel
  rw [h, smul_smul]
  congr 1; ring

end LatticeSystem.Quantum
