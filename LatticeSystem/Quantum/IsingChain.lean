/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.GibbsState

/-!
# One-dimensional quantum Ising chain on an open boundary

Given a coupling `J : ℝ`, external field `h : ℝ`, and a chain of `N + 1`
sites, the open-chain quantum Ising Hamiltonian is

```
H = -J Σ_{i=0..N-1} σ^z_i σ^z_{i+1} - h Σ_{i=0..N} σ^x_i.
```

Using the `N + 1` parametrization lets the coupling sum `Σ_{i : Fin N}`
automatically reduce to `0` when there is only a single site, so the
definition is uniform.

The main results of this module are:

* `quantumIsingHamiltonian_isHermitian` — self-adjointness of `H` for
  real parameters `J`, `h`.
* `quantumIsingGibbsState β J h N` and its inherited properties
  (Hermiticity, commutativity with `H`, the β = 0 closed form),
  bridging this concrete chain to the abstract Gibbs framework of
  `GibbsState.lean`. See Tasaki, *Physics and Mathematics of Quantum
  Many-Body Systems*, §3.3, p. 80.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-- Site-`i` `σ^z` operator on the `N + 1`-site many-body space. -/
noncomputable def spinZ (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (N + 1)) :=
  onSite i pauliZ

/-- Site-`i` `σ^x` operator on the `N + 1`-site many-body space. -/
noncomputable def spinX (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (N + 1)) :=
  onSite i pauliX

/-- Each single-site `σ^z` operator is Hermitian. -/
theorem spinZ_isHermitian (i : Fin (N + 1)) : (spinZ N i).IsHermitian :=
  onSite_isHermitian i pauliZ_isHermitian

/-- Each single-site `σ^x` operator is Hermitian. -/
theorem spinX_isHermitian (i : Fin (N + 1)) : (spinX N i).IsHermitian :=
  onSite_isHermitian i pauliX_isHermitian

/-- `i.castSucc` and `i.succ` are distinct elements of `Fin (N + 1)`. -/
theorem castSucc_ne_succ (i : Fin N) :
    (i.castSucc : Fin (N + 1)) ≠ i.succ := by
  intro heq
  have hval : (i.castSucc : Fin (N + 1)).val = (i.succ : Fin (N + 1)).val :=
    congr_arg Fin.val heq
  simp [Fin.castSucc, Fin.succ] at hval

/-- Nearest-neighbour `σ^z` operators at sites `i` and `i+1` commute. -/
theorem spinZ_mul_spinZ_succ_commute (i : Fin N) :
    spinZ N i.castSucc * spinZ N i.succ = spinZ N i.succ * spinZ N i.castSucc :=
  onSite_mul_onSite_of_ne (castSucc_ne_succ i) pauliZ pauliZ

/-- Nearest-neighbour `σ^z σ^z` is Hermitian. -/
theorem spinZ_mul_spinZ_succ_isHermitian (i : Fin N) :
    (spinZ N i.castSucc * spinZ N i.succ).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute
    (spinZ_isHermitian _) (spinZ_isHermitian _) (spinZ_mul_spinZ_succ_commute i)

/-- The quantum Ising Hamiltonian on an open chain of `N + 1` sites. -/
noncomputable def quantumIsingHamiltonian (N : ℕ) (J h : ℝ) :
    ManyBodyOp (Fin (N + 1)) :=
  (-(J : ℂ)) • ∑ i : Fin N, spinZ N i.castSucc * spinZ N i.succ
    + (-(h : ℂ)) • ∑ i : Fin (N + 1), spinX N i

/-! ## Helpers for Hermiticity under sums and real scalar multiples -/

/-- Hermiticity is preserved under finite sums. -/
private lemma isHermitian_sum {ι : Type*} {n : Type*}
    (s : Finset ι) {f : ι → Matrix n n ℂ} (hf : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns]
    refine Matrix.IsHermitian.add (hf a (Finset.mem_insert_self a t)) ?_
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Hermiticity is preserved under `Finset.univ` sums. -/
private lemma isHermitian_univ_sum {ι : Type*} [Fintype ι] {n : Type*}
    {f : ι → Matrix n n ℂ} (hf : ∀ i, (f i).IsHermitian) :
    (∑ i, f i).IsHermitian :=
  isHermitian_sum Finset.univ (fun i _ => hf i)

/-- Scaling a Hermitian matrix by a real scalar preserves Hermiticity. -/
private lemma isHermitian_smul_real {n : Type*}
    (c : ℝ) {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ((c : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM]
  congr 1
  simp

/-- The quantum Ising Hamiltonian is Hermitian. -/
theorem quantumIsingHamiltonian_isHermitian (N : ℕ) (J h : ℝ) :
    (quantumIsingHamiltonian N J h).IsHermitian := by
  unfold quantumIsingHamiltonian
  refine Matrix.IsHermitian.add ?_ ?_
  · have hsum : (∑ i : Fin N,
        spinZ N i.castSucc * spinZ N i.succ).IsHermitian :=
      isHermitian_univ_sum (fun i => spinZ_mul_spinZ_succ_isHermitian i)
    have := isHermitian_smul_real (-J) hsum
    simpa using this
  · have hsum : (∑ i : Fin (N + 1), spinX N i).IsHermitian :=
      isHermitian_univ_sum (fun i => spinX_isHermitian i)
    have := isHermitian_smul_real (-h) hsum
    simpa using this

/-! ## Gibbs state for the quantum Ising chain -/

/-- The Gibbs state of the open-boundary 1D quantum Ising chain on
`Fin (N + 1)` sites with real coupling `J`, transverse field `h`, and
inverse temperature `β`. -/
noncomputable def quantumIsingGibbsState (β J h : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 1)) :=
  gibbsState β (quantumIsingHamiltonian N J h)

/-- The Ising-chain Gibbs state is Hermitian. -/
theorem quantumIsingGibbsState_isHermitian (β J h : ℝ) (N : ℕ) :
    (quantumIsingGibbsState β J h N).IsHermitian :=
  gibbsState_isHermitian (quantumIsingHamiltonian_isHermitian N J h) β

/-- The Ising-chain Gibbs state commutes with its Hamiltonian. -/
theorem quantumIsingGibbsState_commute_hamiltonian (β J h : ℝ) (N : ℕ) :
    Commute (quantumIsingGibbsState β J h N) (quantumIsingHamiltonian N J h) :=
  gibbsState_commute_hamiltonian β (quantumIsingHamiltonian N J h)

/-- Infinite-temperature (β = 0) closed form for the Ising-chain
expectation: `⟨A⟩_0 = (1/dim) · Tr A` for any observable `A`,
independent of `J` and `h`. -/
theorem quantumIsingGibbsExpectation_zero (J h : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation 0 (quantumIsingHamiltonian N J h) A
      = ((Fintype.card (Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (quantumIsingHamiltonian N J h) A

/-- For any Hermitian observable `O`, the Ising-chain expectation
`⟨O⟩_β` is real (imaginary part vanishes). -/
theorem quantumIsingGibbsExpectation_im_of_isHermitian
    (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h) O).im = 0 :=
  gibbsExpectation_im_of_isHermitian (quantumIsingHamiltonian_isHermitian N J h) hO β

/-- Ising-chain conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem quantumIsingGibbsExpectation_commutator_hamiltonian
    (β J h : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h * A - A * quantumIsingHamiltonian N J h) = 0 :=
  gibbsExpectation_commutator_hamiltonian β (quantumIsingHamiltonian N J h) A

/-- Ising-chain energy expectation is real: `(⟨H_Ising⟩_β).im = 0`. -/
theorem quantumIsingGibbsExpectation_hamiltonian_im (β J h : ℝ) (N : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h)).im = 0 :=
  gibbsExpectation_hamiltonian_im (quantumIsingHamiltonian_isHermitian N J h) β

/-- For Hermitian `O`, the Ising-chain expectation `⟨H_Ising · O⟩_β` is real. -/
theorem quantumIsingGibbsExpectation_mul_hamiltonian_im
    (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im (quantumIsingHamiltonian_isHermitian N J h) hO β

/-- Ising-chain energy-squared expectation is real:
`(⟨H_Ising^2⟩_β).im = 0`. -/
theorem quantumIsingGibbsExpectation_hamiltonian_sq_im (β J h : ℝ) (N : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        ((quantumIsingHamiltonian N J h)^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h)
    (quantumIsingHamiltonian_isHermitian N J h) β

/-- Ising-chain energy n-th power expectation is real:
`(⟨H_Ising^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem quantumIsingGibbsExpectation_hamiltonian_pow_im
    (β J h : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        ((quantumIsingHamiltonian N J h)^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h)
    (quantumIsingHamiltonian_isHermitian N J h) β n

/-- Ising-chain anticommutator expectation is real:
for Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem quantumIsingGibbsExpectation_anticommutator_im
    (β J h : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (quantumIsingHamiltonian_isHermitian N J h) hA hB β

/-- Ising-chain commutator expectation is purely imaginary:
for Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem quantumIsingGibbsExpectation_commutator_re
    (β J h : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (quantumIsingHamiltonian_isHermitian N J h) hA hB β

/-- Ising-chain energy expectation as a sum of bond and transverse-field
contributions:
`⟨H_Ising⟩_β = (-J) · ∑ ⟨σ^z_i σ^z_{i+1}⟩_β + (-h) · ∑ ⟨σ^x_i⟩_β`. -/
theorem quantumIsingGibbsExpectation_self_eq (β J h : ℝ) (N : ℕ) :
    gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h) =
      (-(J : ℂ)) * (∑ i : Fin N,
          gibbsExpectation β (quantumIsingHamiltonian N J h)
            (spinZ N i.castSucc * spinZ N i.succ))
        + (-(h : ℂ)) * (∑ i : Fin (N + 1),
            gibbsExpectation β (quantumIsingHamiltonian N J h) (spinX N i)) := by
  unfold quantumIsingHamiltonian
  rw [gibbsExpectation_add, gibbsExpectation_smul, gibbsExpectation_sum,
    gibbsExpectation_smul, gibbsExpectation_sum]

/-- Ising-chain energy variance is real: `(Var_β(H_Ising)).im = 0`. -/
theorem quantumIsingGibbsHamiltonianVariance_im (β J h : ℝ) (N : ℕ) :
    (gibbsVariance β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h)).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h)
    (quantumIsingHamiltonian_isHermitian N J h) β

/-- Ising-chain partition function is real:
`(partitionFn β H_Ising).im = 0`. -/
theorem quantumIsing_partitionFn_im (β J h : ℝ) (N : ℕ) :
    (partitionFn β (quantumIsingHamiltonian N J h)).im = 0 :=
  partitionFn_im_of_isHermitian (quantumIsingHamiltonian_isHermitian N J h) β

/-- Ising-chain expectation real-cast equality:
for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem quantumIsingGibbsExpectation_ofReal_re_eq
    (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (((gibbsExpectation β (quantumIsingHamiltonian N J h) O).re : ℂ))
      = gibbsExpectation β (quantumIsingHamiltonian N J h) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h) hO β

/-- Ising-chain Rényi-n trace identity:
`Tr(ρ_β^n) = Z(n β) / Z(β)^n`. -/
theorem quantumIsingGibbsState_pow_trace (β J h : ℝ) (N : ℕ) (n : ℕ) :
    ((quantumIsingGibbsState β J h N)^n).trace
      = partitionFn ((n : ℝ) * β) (quantumIsingHamiltonian N J h)
        / (partitionFn β (quantumIsingHamiltonian N J h)) ^ n :=
  gibbsState_pow_trace β (quantumIsingHamiltonian N J h) n

end LatticeSystem.Quantum
