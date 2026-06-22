import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpin

/-!
# Sublattice spin ladder properties: annihilation / adjoint / shift (foundation)

Foundational layer extracted from `SublatticeSpinLadderProperties.lean` for build speed.
This file collects the sublattice-ladder annihilation of extreme-`A`-value configurations,
the sublattice-ladder adjoint relations, the annihilation of extremal states, and the
magnetization-subspace shift by the sublattice ladder operators.

The spin-`1/2` Cartan identity for sublattice ladders and the cross-sublattice ladder
commutativity are kept in the capstone module `SublatticeSpinLadderProperties.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Sublattice ladder annihilates configurations with extreme A-values -/

/-- `Ŝ_A^+ · basisVec σ = 0` when `σ x = 0` for all `x ∈ A`. -/
theorem sublatticeSpinHalfOpPlus_mulVec_basisVec_zero_on (A : Λ → Bool)
    {σ : Λ → Fin 2} (hσ : ∀ x, A x = true → σ x = 0) :
    (sublatticeSpinHalfOpPlus A).mulVec (basisVec σ) = 0 := by
  unfold sublatticeSpinHalfOpPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    rw [onSite_spinHalfOpPlus_mulVec_basisVec]
    rw [if_neg]
    rw [hσ x hA]
    decide
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-- `Ŝ_A^- · basisVec σ = 0` when `σ x = 1` for all `x ∈ A`. -/
theorem sublatticeSpinHalfOpMinus_mulVec_basisVec_one_on (A : Λ → Bool)
    {σ : Λ → Fin 2} (hσ : ∀ x, A x = true → σ x = 1) :
    (sublatticeSpinHalfOpMinus A).mulVec (basisVec σ) = 0 := by
  unfold sublatticeSpinHalfOpMinus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    rw [onSite_spinHalfOpMinus_mulVec_basisVec]
    rw [if_neg]
    rw [hσ x hA]
    decide
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-! ## Sublattice ladder adjoint relations -/

/-- `(Ŝ_A^+)† = Ŝ_A^-`: the spin-`1/2` sublattice raising and lowering
operators are Hermitian conjugates. Mirror of γ-4 step 54. -/
theorem sublatticeSpinHalfOpPlus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A).conjTranspose = sublatticeSpinHalfOpMinus A := by
  unfold sublatticeSpinHalfOpPlus sublatticeSpinHalfOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSite_conjTranspose, spinHalfOpPlus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-- `(Ŝ_A^-)† = Ŝ_A^+`. -/
theorem sublatticeSpinHalfOpMinus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A).conjTranspose = sublatticeSpinHalfOpPlus A := by
  unfold sublatticeSpinHalfOpPlus sublatticeSpinHalfOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSite_conjTranspose, spinHalfOpMinus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder operators annihilate extremal states -/

/-- `Ŝ_A^+ · |0...0⟩ = 0`: the sublattice raising operator annihilates
the all-up basis vector. Spin-`1/2` mirror of γ-4 step 45. -/
theorem sublatticeSpinHalfOpPlus_mulVec_basisVec_zero (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
  unfold sublatticeSpinHalfOpPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    rw [onSite_spinHalfOpPlus_mulVec_basisVec]
    simp
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-- `Ŝ_A^- · |1...1⟩ = 0`: the sublattice lowering operator annihilates
the all-down basis vector. -/
theorem sublatticeSpinHalfOpMinus_mulVec_basisVec_one (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
  unfold sublatticeSpinHalfOpMinus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    rw [onSite_spinHalfOpMinus_mulVec_basisVec]
    simp
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-! ## Sublattice ladder operators shift the magnetization subspace -/

/-- `Ŝ_A^- · v ∈ magnetizationSubspace Λ (M − 1)` for `v ∈ magnetizationSubspace Λ M`.
Spin-`1/2` mirror of γ-4 step 48. -/
theorem sublatticeSpinHalfOpMinus_mulVec_mem_magnetizationSubspace_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (sublatticeSpinHalfOpMinus A).mulVec v ∈ magnetizationSubspace Λ (M - 1) := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  have h := totalSpinHalfOp3_commutator_sublatticeSpinHalfOpMinus A
  have hcomm : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A =
      sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ - sublatticeSpinHalfOpMinus A := by
    have hadd : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A =
        (totalSpinHalfOp3 Λ * sublatticeSpinHalfOpMinus A -
          sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ) +
        sublatticeSpinHalfOpMinus A * totalSpinHalfOp3 Λ := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- `Ŝ_A^+ · v ∈ magnetizationSubspace Λ (M + 1)` for `v ∈ magnetizationSubspace Λ M`. -/
theorem sublatticeSpinHalfOpPlus_mulVec_mem_magnetizationSubspace_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (sublatticeSpinHalfOpPlus A).mulVec v ∈ magnetizationSubspace Λ (M + 1) := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  have h := totalSpinHalfOp3_commutator_sublatticeSpinHalfOpPlus A
  have hcomm : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A =
      sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ + sublatticeSpinHalfOpPlus A := by
    have hadd : totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A =
        (totalSpinHalfOp3 Λ * sublatticeSpinHalfOpPlus A -
          sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ) +
        sublatticeSpinHalfOpPlus A * totalSpinHalfOp3 Λ := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

end LatticeSystem.Quantum
