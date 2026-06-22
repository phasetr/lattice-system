import LatticeSystem.Quantum.HeisenbergChain.EigenvaluesCore

/-!
# Heisenberg-chain explicit forms and eigenvalues (Tasaki §2.4)

Explicit small-N forms (`Fin 2`, `Fin 3`), all-up eigenvalue
calculation, ladder iterates with explicit eigenvalue, and chain
Heisenberg sector-preservation lemmas.

(Refactor Phase 2 PR 17 — second HeisenbergChain extraction,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Open chain Heisenberg ladder iterates with explicit eigenvalue

Combining the iterated lowering ladder (`heisenbergHamiltonian_mulVec_
totalSpinHalfOpMinus_pow_basisVec_const`, PR #82) with the explicit
eigenvalue computation above gives the unnormalised Tasaki §2.4
eq. (2.4.9) ferromagnetic ground states with their explicit chain
eigenvalue `-(N·J/2)`. -/

/-- The unnormalised iterates `(Ŝtot^-)^k · |↑..↑⟩` are
H-eigenvectors of the open chain Heisenberg Hamiltonian with
eigenvalue `-(N·J/2)`. Tasaki §2.4 eq. (2.4.9), p. 33, made explicit
for the chain. -/
theorem openChainHeisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up
    (N : ℕ) (J : ℝ) (k : ℕ) :
    (heisenbergHamiltonian (openChainCoupling N J)).mulVec
        (((totalSpinHalfOpMinus (Fin (N + 1))) ^ k).mulVec
          (basisVec (fun _ : Fin (N + 1) => (0 : Fin 2)))) =
      (-(N * J / 2 : ℂ)) •
        ((totalSpinHalfOpMinus (Fin (N + 1))) ^ k).mulVec
          (basisVec (fun _ : Fin (N + 1) => (0 : Fin 2))) := by
  have hpow := heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_const
    (Λ := Fin (N + 1)) (openChainCoupling N J) 0 k
  -- Goal: H · ((Ŝtot^-)^k · |↑..↑⟩) = -(N·J/2) • ((Ŝtot^-)^k · |↑..↑⟩).
  rw [hpow]
  -- Now goal is: c_J • ... = -(N·J/2) • ... where c_J = Σ_{x,y} J(x,y) χ_{x,y}.
  -- We need to show c_J = -(N·J/2).
  congr 1
  -- Compute c_J using openChainCoupling_sum_eq + diagonal vanishing.
  have hdiag : ∀ x : Fin (N + 1), openChainCoupling N J x x = 0 := by
    intro x
    rw [openChainCoupling_apply]
    rw [if_neg (by simp)]
  have hsame : ∀ x y : Fin (N + 1),
      openChainCoupling N J x y *
        (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) =
      (1 / 4 : ℂ) * openChainCoupling N J x y := by
    intro x y
    by_cases h : x = y
    · subst h
      rw [if_pos rfl, hdiag]; ring
    · rw [if_neg h]; ring
  simp_rw [hsame]
  rw [show (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (1 / 4 : ℂ) * openChainCoupling N J x y) =
      (1 / 4 : ℂ) * (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        openChainCoupling N J x y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]]
  rw [openChainCoupling_sum_eq N J]
  ring

/-- The dual ladder iterates `(Ŝtot^+)^k · |↓..↓⟩` are also
H-eigenvectors of the open chain Heisenberg Hamiltonian with
eigenvalue `-(N·J/2)`. -/
theorem openChainHeisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down
    (N : ℕ) (J : ℝ) (k : ℕ) :
    (heisenbergHamiltonian (openChainCoupling N J)).mulVec
        (((totalSpinHalfOpPlus (Fin (N + 1))) ^ k).mulVec
          (basisVec (fun _ : Fin (N + 1) => (1 : Fin 2)))) =
      (-(N * J / 2 : ℂ)) •
        ((totalSpinHalfOpPlus (Fin (N + 1))) ^ k).mulVec
          (basisVec (fun _ : Fin (N + 1) => (1 : Fin 2))) := by
  have hpow := heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_const
    (Λ := Fin (N + 1)) (openChainCoupling N J) 1 k
  rw [hpow]
  congr 1
  have hdiag : ∀ x : Fin (N + 1), openChainCoupling N J x x = 0 := by
    intro x
    rw [openChainCoupling_apply]
    rw [if_neg (by simp)]
  have hsame : ∀ x y : Fin (N + 1),
      openChainCoupling N J x y *
        (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) =
      (1 / 4 : ℂ) * openChainCoupling N J x y := by
    intro x y
    by_cases h : x = y
    · subst h
      rw [if_pos rfl, hdiag]; ring
    · rw [if_neg h]; ring
  simp_rw [hsame]
  rw [show (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (1 / 4 : ℂ) * openChainCoupling N J x y) =
      (1 / 4 : ℂ) * (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        openChainCoupling N J x y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]]
  rw [openChainCoupling_sum_eq N J]
  ring

/-! ## Chain Heisenberg preserves magnetisation sectors (Tasaki §2.2 (2.2.10))

Both the open and periodic chain Heisenberg Hamiltonians preserve
every magnetisation subspace `H_M`. Direct consequence of
`heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem`
(PR #91) applied to the chain couplings. -/

/-- The open chain Heisenberg Hamiltonian preserves every
magnetisation subspace `H_M` (SU(2) invariance). -/
theorem openChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem
    (N : ℕ) (J : ℝ) {M : ℂ} {v : (Fin (N + 1) → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace (Fin (N + 1)) M) :
    (heisenbergHamiltonian (openChainCoupling N J)).mulVec v ∈
      magnetizationSubspace (Fin (N + 1)) M :=
  heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem (Fin (N + 1))
    (openChainCoupling N J) hv

/-- The periodic chain Heisenberg Hamiltonian preserves every
magnetisation subspace `H_M` (SU(2) invariance). -/
theorem periodicChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem
    (N : ℕ) (J : ℝ) {M : ℂ} {v : (Fin (N + 2) → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace (Fin (N + 2)) M) :
    (heisenbergHamiltonian (periodicChainCoupling N J)).mulVec v ∈
      magnetizationSubspace (Fin (N + 2)) M :=
  heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem (Fin (N + 2))
    (periodicChainCoupling N J) hv


end LatticeSystem.Quantum
