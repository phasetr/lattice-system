/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
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

end LatticeSystem.Quantum
