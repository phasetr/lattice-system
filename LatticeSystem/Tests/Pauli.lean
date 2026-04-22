/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.Pauli

/-!
# Test coverage for Quantum/Pauli

A+B+D coverage for `pauliX`, `pauliY`, `pauliZ` (per refactor plan
v4 §9 mapping table; refactor Phase 1 PR 13, #281).
-/

namespace LatticeSystem.Tests.Pauli

open LatticeSystem.Quantum Complex

/-! ## D. Hermiticity, square = 1, cyclic products, anticomm -/

example : pauliX.IsHermitian := pauliX_isHermitian
example : pauliY.IsHermitian := pauliY_isHermitian
example : pauliZ.IsHermitian := pauliZ_isHermitian

example : pauliX * pauliX = 1 := pauliX_mul_self
example : pauliY * pauliY = 1 := pauliY_mul_self
example : pauliZ * pauliZ = 1 := pauliZ_mul_self

example : pauliX * pauliY = I • pauliZ := pauliX_mul_pauliY
example : pauliY * pauliZ = I • pauliX := pauliY_mul_pauliZ
example : pauliZ * pauliX = I • pauliY := pauliZ_mul_pauliX

example : pauliX * pauliY + pauliY * pauliX = 0 :=
  pauliX_anticomm_pauliY
example : pauliY * pauliZ + pauliZ * pauliY = 0 :=
  pauliY_anticomm_pauliZ
example : pauliZ * pauliX + pauliX * pauliZ = 0 :=
  pauliZ_anticomm_pauliX

/-! ## A + B. matrix entry-wise on `Fin 2 × Fin 2` -/

example : pauliX = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX]

example : pauliY = !![0, -I; I, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY]

example : pauliZ = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ]

end LatticeSystem.Tests.Pauli
