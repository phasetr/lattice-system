/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Single-site Pauli operators

This module introduces the three Pauli matrices acting on the single-site
spin-1/2 Hilbert space `ℂ^2`, and proves the basic algebraic relations:

* Hermiticity `σ^α = (σ^α)†`,
* involutivity `σ^α * σ^α = 1`,
* anticommutation `σ^α σ^β + σ^β σ^α = 0` for `α ≠ β`,
* the cyclic products `σ^x σ^y = i σ^z`, `σ^y σ^z = i σ^x`, `σ^z σ^x = i σ^y`.

These are the algebraic building blocks from which finite-chain quantum
Ising / Heisenberg Hamiltonians will be assembled in later modules.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-- The Pauli-X matrix `σ^x = ((0, 1), (1, 0))`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Pauli-Y matrix `σ^y = ((0, -i), (i, 0))`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- The Pauli-Z matrix `σ^z = ((1, 0), (0, -1))`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-! ## Hermiticity -/

/-- The Pauli-X matrix is Hermitian: `(σ^x)† = σ^x`. -/
theorem pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

/-- The Pauli-Y matrix is Hermitian: `(σ^y)† = σ^y`. -/
theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY]

/-- The Pauli-Z matrix is Hermitian: `(σ^z)† = σ^z`. -/
theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

/-! ## Involutivity (`σ^α * σ^α = 1`) -/

/-- `σ^x * σ^x = 1`. -/
@[simp]
theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ^y * σ^y = 1`. -/
@[simp]
theorem pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `σ^z * σ^z = 1`. -/
@[simp]
theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Cyclic products (`σ^α σ^β = i σ^γ` for `(α,β,γ)` a cyclic permutation) -/

/-- `σ^x * σ^y = i • σ^z`. -/
theorem pauliX_mul_pauliY : pauliX * pauliY = I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ^y * σ^z = i • σ^x`. -/
theorem pauliY_mul_pauliZ : pauliY * pauliZ = I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ^z * σ^x = i • σ^y`. -/
theorem pauliZ_mul_pauliX : pauliZ * pauliX = I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Anticommutators (`σ^α σ^β + σ^β σ^α = 0` for `α ≠ β`) -/

/-- `σ^x * σ^y + σ^y * σ^x = 0`. -/
theorem pauliX_anticomm_pauliY : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY]

/-- `σ^y * σ^z + σ^z * σ^y = 0`. -/
theorem pauliY_anticomm_pauliZ : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, pauliZ]

/-- `σ^z * σ^x + σ^x * σ^z = 0`. -/
theorem pauliZ_anticomm_pauliX : pauliZ * pauliX + pauliX * pauliZ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ]

end LatticeSystem.Quantum
