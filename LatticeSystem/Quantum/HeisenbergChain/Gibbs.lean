/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.GibbsState.Covariance

/-!
# 1D Heisenberg chain Gibbs state machinery

The open-chain and periodic-chain Heisenberg Gibbs states +
their full expectation companion families (energy, Hermiticity,
commute-with-H, β=0 closed form, im-of-Hermitian, conservation,
hamiltonian power im, partition function im, etc.).

(Refactor Phase 2 PR 23 — third HeisenbergChain extraction,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

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
