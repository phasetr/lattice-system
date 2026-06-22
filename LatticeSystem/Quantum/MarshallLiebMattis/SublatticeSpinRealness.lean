import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinRealnessCore

/-!
# Realness of sublattice spin-`1/2` operator matrix elements + conjTranspose squared

Companion file split off from `MarshallLiebMattis.SublatticeSpin` (1074 → ~918 + 158 lines) to
shrink that module's compilation footprint.  All declarations here are leaves: they have no
downstream Lean consumers in the repository (only `docs/index.md` references some by name).  No
behaviour changes — every theorem keeps its original namespace `LatticeSystem.Quantum`, name, and
statement, so call sites elsewhere see no diff.

Contents:
* `sublatticeSpinHalfOp{1,2,3}_sq_eq_conjTranspose_mul` — squared sublattice axis operator as a
  Hermitian conjugate-product, directly from `sublatticeSpinHalfOp{1,2,3}_isHermitian`.
* Matrix-element realness for the axis-1, axis-3 sublattice operators (with single-site +
  on-site building blocks).
* Matrix-element realness for the sublattice ladder operators `Ŝ_A^±` (with single-site + on-site
  building blocks).

The four imaginary-zero entry points are the spin-`1/2` mirror of the spin-`S` realness chain in
`Quantum/SpinS/...` (γ-4 step 57).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Sublattice ladder matrix element realness -/

/-- The single-site spin-`1/2` raising operator has real entries. -/
private theorem spinHalfOpPlus_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOpPlus i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOpPlus]

/-- The single-site spin-`1/2` lowering operator has real entries. -/
private theorem spinHalfOpMinus_apply_im_eq_zero (i j : Fin 2) :
    (spinHalfOpMinus i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinHalfOpMinus]

/-- The on-site embedded `Ŝ^+` has real matrix elements. -/
theorem onSite_spinHalfOpPlus_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOpPlus : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOpPlus_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]
    simp

/-- The on-site embedded `Ŝ^-` has real matrix elements. -/
theorem onSite_spinHalfOpMinus_apply_im_eq_zero (x : Λ)
    (σ' σ : Λ → Fin 2) :
    ((onSite x spinHalfOpMinus : ManyBodyOp Λ) σ' σ).im = 0 := by
  rw [onSite_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    exact spinHalfOpMinus_apply_im_eq_zero (σ' x) (σ x)
  · rw [if_neg h]
    simp

/-- The sublattice raising operator has real matrix elements:
`((Ŝ_A^+) σ' σ).im = 0`. Spin-`1/2` mirror of γ-4 step 57. -/
theorem sublatticeSpinHalfOpPlus_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOpPlus A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOpPlus
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOpPlus_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-- The sublattice lowering operator has real matrix elements:
`((Ŝ_A^-) σ' σ).im = 0`. -/
theorem sublatticeSpinHalfOpMinus_apply_im_eq_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin 2) :
    ((sublatticeSpinHalfOpMinus A) σ' σ).im = 0 := by
  unfold sublatticeSpinHalfOpMinus
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSite_spinHalfOpMinus_apply_im_eq_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

end LatticeSystem.Quantum
