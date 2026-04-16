/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases

/-!
# 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq (2.1.28))

The π-rotations of Euclidean 3-space about the coordinate axes:

```
R^(1)_π = !![1, 0, 0; 0, -1, 0; 0, 0, -1]
R^(2)_π = !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
R^(3)_π = !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
```

These are 3×3 real orthogonal matrices. They satisfy
`(R^(α)_π)² = 1`, `R^(1)_π · R^(2)_π = R^(3)_π`, and the two cyclic
analogues (Problem 2.1.f).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- 3D π-rotation about axis 1. -/
def rot3D1Pi : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, -1]

/-- 3D π-rotation about axis 2. -/
def rot3D2Pi : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- 3D π-rotation about axis 3. -/
def rot3D3Pi : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 0;
     0, -1, 0;
     0, 0, 1]

/-! ## Squared π-rotations -/

/-- `(R^(1)_π)² = 1`. -/
theorem rot3D1Pi_sq : rot3D1Pi * rot3D1Pi = 1 := by
  unfold rot3D1Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `(R^(2)_π)² = 1`. -/
theorem rot3D2Pi_sq : rot3D2Pi * rot3D2Pi = 1 := by
  unfold rot3D2Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `(R^(3)_π)² = 1`. -/
theorem rot3D3Pi_sq : rot3D3Pi * rot3D3Pi = 1 := by
  unfold rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## Products form a `Z₂ × Z₂` group (Tasaki §2.1 Problem 2.1.f) -/

/-- `R^(1)_π · R^(2)_π = R^(3)_π`. -/
theorem rot3D1Pi_mul_rot3D2Pi : rot3D1Pi * rot3D2Pi = rot3D3Pi := by
  unfold rot3D1Pi rot3D2Pi rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `R^(2)_π · R^(3)_π = R^(1)_π`. -/
theorem rot3D2Pi_mul_rot3D3Pi : rot3D2Pi * rot3D3Pi = rot3D1Pi := by
  unfold rot3D1Pi rot3D2Pi rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `R^(3)_π · R^(1)_π = R^(2)_π`. -/
theorem rot3D3Pi_mul_rot3D1Pi : rot3D3Pi * rot3D1Pi = rot3D2Pi := by
  unfold rot3D1Pi rot3D2Pi rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## Commutativity of distinct-axis π-rotations -/

/-- `R^(1)_π · R^(2)_π = R^(2)_π · R^(1)_π`. -/
theorem rot3D1Pi_comm_rot3D2Pi : rot3D1Pi * rot3D2Pi = rot3D2Pi * rot3D1Pi := by
  rw [rot3D1Pi_mul_rot3D2Pi]
  unfold rot3D1Pi rot3D2Pi rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `R^(2)_π · R^(3)_π = R^(3)_π · R^(2)_π`. -/
theorem rot3D2Pi_comm_rot3D3Pi : rot3D2Pi * rot3D3Pi = rot3D3Pi * rot3D2Pi := by
  rw [rot3D2Pi_mul_rot3D3Pi]
  unfold rot3D1Pi rot3D2Pi rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `R^(3)_π · R^(1)_π = R^(1)_π · R^(3)_π`. -/
theorem rot3D3Pi_comm_rot3D1Pi : rot3D3Pi * rot3D1Pi = rot3D1Pi * rot3D3Pi := by
  rw [rot3D3Pi_mul_rot3D1Pi]
  unfold rot3D1Pi rot3D2Pi rot3D3Pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## General-θ 3D rotation matrices R^(α)_θ (Tasaki eq (2.1.11)) -/

/-- 3D rotation by angle `θ` about axis 3. -/
noncomputable def rot3D3 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0;
     Real.sin θ,  Real.cos θ, 0;
     0,           0,          1]

/-- 3D rotation by angle `θ` about axis 1. -/
noncomputable def rot3D1 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,          0,           0;
     0, Real.cos θ, -Real.sin θ;
     0, Real.sin θ,  Real.cos θ]

/-- 3D rotation by angle `θ` about axis 2. -/
noncomputable def rot3D2 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, Real.sin θ;
     0,          1,          0;
     -Real.sin θ, 0, Real.cos θ]

/-- `R^(3)_0 = 1`. -/
theorem rot3D3_zero : rot3D3 0 = 1 := by
  unfold rot3D3
  simp only [Real.cos_zero, Real.sin_zero, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `R^(1)_0 = 1`. -/
theorem rot3D1_zero : rot3D1 0 = 1 := by
  unfold rot3D1
  simp only [Real.cos_zero, Real.sin_zero, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `R^(2)_0 = 1`. -/
theorem rot3D2_zero : rot3D2 0 = 1 := by
  unfold rot3D2
  simp only [Real.cos_zero, Real.sin_zero, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `R^(3)_π` from the general formula equals the explicit π-rotation. -/
theorem rot3D3_pi : rot3D3 Real.pi = rot3D3Pi := by
  unfold rot3D3 rot3D3Pi
  simp [Real.cos_pi, Real.sin_pi]

/-- `R^(1)_π` from the general formula equals the explicit π-rotation. -/
theorem rot3D1_pi : rot3D1 Real.pi = rot3D1Pi := by
  unfold rot3D1 rot3D1Pi
  simp [Real.cos_pi, Real.sin_pi]

/-- `R^(2)_π` from the general formula equals the explicit π-rotation. -/
theorem rot3D2_pi : rot3D2 Real.pi = rot3D2Pi := by
  unfold rot3D2 rot3D2Pi
  simp [Real.cos_pi, Real.sin_pi]

end LatticeSystem.Quantum
