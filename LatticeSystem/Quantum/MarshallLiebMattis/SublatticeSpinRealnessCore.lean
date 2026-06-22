import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpin

/-!
# Sublattice spin realness: axis-squared and axis-1/3 (foundation)

Foundational layer extracted from `SublatticeSpinRealness.lean` for build speed.  This file
proves the sublattice axis squared as a `conjTranspose` product and the matrix-element realness
of the sublattice axis-1 / axis-3 operators.

The sublattice ladder matrix-element realness is kept in the capstone module
`SublatticeSpinRealness.lean`.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Sublattice axis squared as conjTranspose product -/

/-- `(Ŝ_A^(1))² = (Ŝ_A^(1))ᴴ * Ŝ_A^(1)`. Direct from Hermiticity. -/
theorem sublatticeSpinHalfOp1_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A =
      (sublatticeSpinHalfOp1 A).conjTranspose * sublatticeSpinHalfOp1 A := by
  rw [(sublatticeSpinHalfOp1_isHermitian A).eq]

theorem sublatticeSpinHalfOp2_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A =
      (sublatticeSpinHalfOp2 A).conjTranspose * sublatticeSpinHalfOp2 A := by
  rw [(sublatticeSpinHalfOp2_isHermitian A).eq]

theorem sublatticeSpinHalfOp3_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 A =
      (sublatticeSpinHalfOp3 A).conjTranspose * sublatticeSpinHalfOp3 A := by
  rw [(sublatticeSpinHalfOp3_isHermitian A).eq]

/-! ## Sublattice axis-1 / axis-3 matrix element realness -/

/-- The single-site spin-`1/2` axis-1 operator has real entries. -/
private theorem spinHalfOp1_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOp1 i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp1, pauliX]

/-- The single-site spin-`1/2` axis-3 operator has real entries. -/
private theorem spinHalfOp3_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOp3 i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp3, pauliZ]

/-- The on-site embedded `Ŝ^(1)` has real matrix elements. -/
theorem onSite_spinHalfOp1_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOp1 : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOp1_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]; simp

/-- The on-site embedded `Ŝ^(3)` has real matrix elements. -/
theorem onSite_spinHalfOp3_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOp3 : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOp3_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]; simp

/-- The sublattice axis-1 operator has real matrix elements. -/
theorem sublatticeSpinHalfOp1_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOp1 A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOp1
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOp1_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-- The sublattice axis-3 operator has real matrix elements. -/
theorem sublatticeSpinHalfOp3_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOp3 A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOp3
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOp3_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

end LatticeSystem.Quantum
