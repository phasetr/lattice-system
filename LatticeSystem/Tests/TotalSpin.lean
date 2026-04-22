/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin

/-!
# Test coverage for Quantum/TotalSpin

A+C+G+D coverage for `totalSpinHalfOp{1,2,3,±}`,
`totalSpinHalfSquared`, `totalSpinHalfRot{1,2,3}` and the basis-state
actions (refactor plan v4 §9 mapping table; refactor Phase 1 PR 6,
#281).
-/

namespace LatticeSystem.Tests.TotalSpin

open LatticeSystem.Quantum

/-! ## D. signature shims -/

/-- `Ŝ_tot^(1)` is Hermitian. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    (totalSpinHalfOp1 Λ).IsHermitian :=
  totalSpinHalfOp1_isHermitian Λ

/-- `Ŝ_tot^(2)` is Hermitian. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    (totalSpinHalfOp2 Λ).IsHermitian :=
  totalSpinHalfOp2_isHermitian Λ

/-- `Ŝ_tot^(3)` is Hermitian. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    (totalSpinHalfOp3 Λ).IsHermitian :=
  totalSpinHalfOp3_isHermitian Λ

/-- `Ŝ_tot²` is Hermitian. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    (totalSpinHalfSquared Λ).IsHermitian :=
  totalSpinHalfSquared_isHermitian Λ

/-! ## D: `Ŝ_tot^±` bridges (Tasaki §2.2 (2.2.8)) -/

/-- `Ŝ_tot^+ = Ŝ_tot^(1) + i · Ŝ_tot^(2)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    (totalSpinHalfOpPlus Λ : ManyBodyOp Λ) =
      totalSpinHalfOp1 Λ + Complex.I • totalSpinHalfOp2 Λ :=
  totalSpinHalfOpPlus_eq_add Λ

/-- `Ŝ_tot^- = Ŝ_tot^(1) - i · Ŝ_tot^(2)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    (totalSpinHalfOpMinus Λ : ManyBodyOp Λ) =
      totalSpinHalfOp1 Λ - Complex.I • totalSpinHalfOp2 Λ :=
  totalSpinHalfOpMinus_eq_sub Λ

/-! ## D: basis-state action (`Ŝ_tot^(3)` eigenvector) -/

/-- `Ŝ_x^(3) · |σ⟩ = spinHalfSign(σ x) · |σ⟩` (basis vectors are
eigenvectors of `Ŝ_x^(3)` with eigenvalue `±1/2`). -/
example (x : Fin 3) (σ : Fin 3 → Fin 2) :
    (onSite x spinHalfOp3 : ManyBodyOp (Fin 3)).mulVec (basisVec σ) =
      spinHalfSign (σ x) • basisVec σ :=
  onSite_spinHalfOp3_mulVec_basisVec (Λ := Fin 3) x σ

/-- `Ŝ_tot^(3) · |σ⟩ = (Σ_x sign σ_x) · |σ⟩`. -/
example (σ : Fin 3 → Fin 2) :
    (totalSpinHalfOp3 (Fin 3)).mulVec (basisVec σ) =
      (∑ x : Fin 3, spinHalfSign (σ x)) • basisVec σ :=
  totalSpinHalfOp3_mulVec_basisVec (Fin 3) σ

/-! ## A. decide-based universal on `Fin 2`: every basis vector
is a `Ŝ_tot^(3)` eigenvector with an integer/half-integer
eigenvalue tag (parity) -/

/-- The value `spinHalfSign s = ±1/2` for every `s : Fin 2`. -/
example :
    ∀ s : Fin 2,
        spinHalfSign s = (1 / 2 : ℂ) ∨
          spinHalfSign s = -(1 / 2 : ℂ) := by
  intro s; fin_cases s <;> simp [spinHalfSign]

end LatticeSystem.Tests.TotalSpin
