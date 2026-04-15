/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import Mathlib.Tactic.LinearCombination

/-!
# Basis states and raising/lowering operators for S = 1/2

Formalizes Tasaki *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1, eqs. (2.1.4), (2.1.5), (2.1.6), pp. 14.

* Computational-basis column vectors `|ψ^↑⟩ = (1, 0)ᵀ` and
  `|ψ^↓⟩ = (0, 1)ᵀ` (eq. (2.1.6) for `S = 1/2`, `σ = ±1/2`).
* Eigenvalue equation (eq. (2.1.4)):
  `Ŝ^(3) |ψ^↑⟩ = (1/2) |ψ^↑⟩`, `Ŝ^(3) |ψ^↓⟩ = -(1/2) |ψ^↓⟩`.
* Raising and lowering operators `Ŝ^± := Ŝ^(1) ± i · Ŝ^(2)`, proved to
  equal the strictly triangular unit matrices `!![0,1;0,0]` and
  `!![0,0;1,0]`.
* Action (eq. (2.1.5)):
  `Ŝ^+ |ψ^↑⟩ = 0`, `Ŝ^- |ψ^↑⟩ = |ψ^↓⟩`,
  `Ŝ^+ |ψ^↓⟩ = |ψ^↑⟩`, `Ŝ^- |ψ^↓⟩ = 0`.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Basis states (Tasaki eq 2.1.6, p. 14) -/

/-- The computational-basis up state `|ψ^↑⟩ = (1, 0)ᵀ`. -/
def spinHalfUp : Fin 2 → ℂ := ![1, 0]

/-- The computational-basis down state `|ψ^↓⟩ = (0, 1)ᵀ`. -/
def spinHalfDown : Fin 2 → ℂ := ![0, 1]

/-! ## Eigenvalue equation (Tasaki eq 2.1.4, p. 14) -/

/-- `Ŝ^(3) |ψ^↑⟩ = (1/2) |ψ^↑⟩`. -/
theorem spinHalfOp3_mulVec_spinHalfUp :
    spinHalfOp3.mulVec spinHalfUp = (1 / 2 : ℂ) • spinHalfUp := by
  ext i
  fin_cases i <;>
    simp [spinHalfOp3, spinHalfUp, pauliZ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.smul_apply]

/-- `Ŝ^(3) |ψ^↓⟩ = -(1/2) |ψ^↓⟩`. -/
theorem spinHalfOp3_mulVec_spinHalfDown :
    spinHalfOp3.mulVec spinHalfDown = -(1 / 2 : ℂ) • spinHalfDown := by
  ext i
  fin_cases i <;>
    simp [spinHalfOp3, spinHalfDown, pauliZ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.smul_apply]

/-! ## Raising and lowering operators (Tasaki p. 14) -/

/-- Raising operator: `Ŝ^+ = (0, 1; 0, 0)` in the computational basis. -/
def spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- Lowering operator: `Ŝ^- = (0, 0; 1, 0)` in the computational basis. -/
def spinHalfOpMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 1, 0]

/-- The defining identity `Ŝ^+ = Ŝ^(1) + i · Ŝ^(2)`. -/
theorem spinHalfOpPlus_eq_add :
    spinHalfOpPlus = spinHalfOp1 + I • spinHalfOp2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOp1, spinHalfOp2, pauliX, pauliY] <;>
    ring_nf <;> (try rw [Complex.I_sq]) <;> ring

/-- The defining identity `Ŝ^- = Ŝ^(1) - i · Ŝ^(2)`. -/
theorem spinHalfOpMinus_eq_sub :
    spinHalfOpMinus = spinHalfOp1 - I • spinHalfOp2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpMinus, spinHalfOp1, spinHalfOp2, pauliX, pauliY] <;>
    ring_nf <;> (try rw [Complex.I_sq]) <;> ring

/-! ## Raising/lowering actions (Tasaki eq 2.1.5, p. 14) -/

/-- `Ŝ^+ |ψ^↑⟩ = 0`. -/
theorem spinHalfOpPlus_mulVec_spinHalfUp :
    spinHalfOpPlus.mulVec spinHalfUp = 0 := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpPlus, spinHalfUp, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- `Ŝ^- |ψ^↑⟩ = |ψ^↓⟩`. -/
theorem spinHalfOpMinus_mulVec_spinHalfUp :
    spinHalfOpMinus.mulVec spinHalfUp = spinHalfDown := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpMinus, spinHalfUp, spinHalfDown, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- `Ŝ^+ |ψ^↓⟩ = |ψ^↑⟩`. -/
theorem spinHalfOpPlus_mulVec_spinHalfDown :
    spinHalfOpPlus.mulVec spinHalfDown = spinHalfUp := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpPlus, spinHalfUp, spinHalfDown, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- `Ŝ^- |ψ^↓⟩ = 0`. -/
theorem spinHalfOpMinus_mulVec_spinHalfDown :
    spinHalfOpMinus.mulVec spinHalfDown = 0 := by
  ext i
  fin_cases i <;>
    simp [spinHalfOpMinus, spinHalfDown, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

end LatticeSystem.Quantum
