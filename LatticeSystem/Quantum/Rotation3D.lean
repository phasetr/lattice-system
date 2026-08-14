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

/-! ## Internal axis-indexed core

The six rotation matrices below are the three instantiations `a = 0, 1, 2` of two
axis-indexed families. The 0-based index `a : Fin 3` corresponds to axis `α = a + 1`
of Tasaki §2.1, and the orientation of the general-θ family is fixed by the cyclic
successor in `Fin 3`, so no axis is ever written out by hand.
-/

/-- Matrix of the π-rotation of Euclidean 3-space about the coordinate axis with 0-based
index `a`: the diagonal matrix fixing the `a`-th coordinate and negating the other two. -/
private def axisRot3DPi (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then (if i = a then 1 else -1) else 0

/-- Matrix of the rotation of Euclidean 3-space by angle `θ` about the coordinate axis with
0-based index `a` (Tasaki §2.1 eq. (2.1.11)). The orientation is fixed by the cyclic order of
`Fin 3`: the entry `-Real.sin θ` sits at `(a + 1, a + 2)` and `+Real.sin θ` at
`(a + 2, a + 1)`. -/
private noncomputable def axisRot3D (a : Fin 3) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if i = a then (if j = a then 1 else 0)
    else if j = a then 0
    else if i = j then Real.cos θ
    else if j = i + 1 then -Real.sin θ
    else Real.sin θ

/-- Every axis π-rotation is an involution. -/
private theorem axisRot3DPi_sq (a : Fin 3) : axisRot3DPi a * axisRot3DPi a = 1 := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [axisRot3DPi, Matrix.mul_apply]

/-- The product of the π-rotations about two cyclically consecutive axes is the π-rotation
about the remaining axis. -/
private theorem axisRot3DPi_mul_succ (a : Fin 3) :
    axisRot3DPi a * axisRot3DPi (a + 1) = axisRot3DPi (a + 2) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [axisRot3DPi, Matrix.mul_apply]

/-- The π-rotations about two cyclically consecutive axes commute. -/
private theorem axisRot3DPi_comm_succ (a : Fin 3) :
    axisRot3DPi a * axisRot3DPi (a + 1) = axisRot3DPi (a + 1) * axisRot3DPi a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [axisRot3DPi, Matrix.mul_apply]

/-- The rotation by angle `0` about any axis is the identity. -/
private theorem axisRot3D_zero (a : Fin 3) : axisRot3D a 0 = 1 := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [axisRot3D]

/-- The rotation by angle `π` about any axis is the corresponding π-rotation. -/
private theorem axisRot3D_pi (a : Fin 3) : axisRot3D a Real.pi = axisRot3DPi a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [axisRot3D, axisRot3DPi]

/-- 3D π-rotation about axis 1. -/
def rot3D1Pi : Matrix (Fin 3) (Fin 3) ℝ :=
  axisRot3DPi 0

/-- 3D π-rotation about axis 2. -/
def rot3D2Pi : Matrix (Fin 3) (Fin 3) ℝ :=
  axisRot3DPi 1

/-- 3D π-rotation about axis 3. -/
def rot3D3Pi : Matrix (Fin 3) (Fin 3) ℝ :=
  axisRot3DPi 2

/-! ## Squared π-rotations -/

/-- `(R^(1)_π)² = 1`. -/
theorem rot3D1Pi_sq : rot3D1Pi * rot3D1Pi = 1 :=
  axisRot3DPi_sq 0

/-- `(R^(2)_π)² = 1`. -/
theorem rot3D2Pi_sq : rot3D2Pi * rot3D2Pi = 1 :=
  axisRot3DPi_sq 1

/-- `(R^(3)_π)² = 1`. -/
theorem rot3D3Pi_sq : rot3D3Pi * rot3D3Pi = 1 :=
  axisRot3DPi_sq 2

/-! ## Products form a `Z₂ × Z₂` group (Tasaki §2.1 Problem 2.1.f) -/

/-- `R^(1)_π · R^(2)_π = R^(3)_π`. -/
theorem rot3D1Pi_mul_rot3D2Pi : rot3D1Pi * rot3D2Pi = rot3D3Pi :=
  axisRot3DPi_mul_succ 0

/-- `R^(2)_π · R^(3)_π = R^(1)_π`. -/
theorem rot3D2Pi_mul_rot3D3Pi : rot3D2Pi * rot3D3Pi = rot3D1Pi :=
  axisRot3DPi_mul_succ 1

/-- `R^(3)_π · R^(1)_π = R^(2)_π`. -/
theorem rot3D3Pi_mul_rot3D1Pi : rot3D3Pi * rot3D1Pi = rot3D2Pi :=
  axisRot3DPi_mul_succ 2

/-! ## Commutativity of distinct-axis π-rotations -/

/-- `R^(1)_π · R^(2)_π = R^(2)_π · R^(1)_π`. -/
theorem rot3D1Pi_comm_rot3D2Pi : rot3D1Pi * rot3D2Pi = rot3D2Pi * rot3D1Pi :=
  axisRot3DPi_comm_succ 0

/-- `R^(2)_π · R^(3)_π = R^(3)_π · R^(2)_π`. -/
theorem rot3D2Pi_comm_rot3D3Pi : rot3D2Pi * rot3D3Pi = rot3D3Pi * rot3D2Pi :=
  axisRot3DPi_comm_succ 1

/-- `R^(3)_π · R^(1)_π = R^(1)_π · R^(3)_π`. -/
theorem rot3D3Pi_comm_rot3D1Pi : rot3D3Pi * rot3D1Pi = rot3D1Pi * rot3D3Pi :=
  axisRot3DPi_comm_succ 2

/-! ## General-θ 3D rotation matrices R^(α)_θ (Tasaki eq (2.1.11)) -/

/-- 3D rotation by angle `θ` about axis 3. -/
noncomputable def rot3D3 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  axisRot3D 2 θ

/-- 3D rotation by angle `θ` about axis 1. -/
noncomputable def rot3D1 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  axisRot3D 0 θ

/-- 3D rotation by angle `θ` about axis 2. -/
noncomputable def rot3D2 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  axisRot3D 1 θ

/-- `R^(3)_0 = 1`. -/
theorem rot3D3_zero : rot3D3 0 = 1 :=
  axisRot3D_zero 2

/-- `R^(1)_0 = 1`. -/
theorem rot3D1_zero : rot3D1 0 = 1 :=
  axisRot3D_zero 0

/-- `R^(2)_0 = 1`. -/
theorem rot3D2_zero : rot3D2 0 = 1 :=
  axisRot3D_zero 1

/-- `R^(3)_π` from the general formula equals the explicit π-rotation. -/
theorem rot3D3_pi : rot3D3 Real.pi = rot3D3Pi :=
  axisRot3D_pi 2

/-- `R^(1)_π` from the general formula equals the explicit π-rotation. -/
theorem rot3D1_pi : rot3D1 Real.pi = rot3D1Pi :=
  axisRot3D_pi 0

/-- `R^(2)_π` from the general formula equals the explicit π-rotation. -/
theorem rot3D2_pi : rot3D2 Real.pi = rot3D2Pi :=
  axisRot3D_pi 1

end LatticeSystem.Quantum
