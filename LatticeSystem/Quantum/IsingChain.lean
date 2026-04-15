/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli

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

The main result of this module is `quantumIsingHamiltonian_isHermitian`,
the self-adjointness of `H` for real parameters `J`, `h`.
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

private lemma isHermitian_univ_sum {ι : Type*} [Fintype ι] {n : Type*}
    {f : ι → Matrix n n ℂ} (hf : ∀ i, (f i).IsHermitian) :
    (∑ i, f i).IsHermitian :=
  isHermitian_sum Finset.univ (fun i _ => hf i)

private lemma isHermitian_smul_real {n : Type*}
    (c : ℝ) {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ((c : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM]
  congr 1
  simp [Complex.star_def]

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

end LatticeSystem.Quantum
