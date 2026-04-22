/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.SpinHalfDecomp

/-!
# Test coverage for the SpinHalf cluster

A+C+G+D coverage for `Quantum/SpinHalf{,Basis,Decomp}.lean` (per
refactor plan v4 §9 mapping table; refactor Phase 1 PR 10, #281).
-/

namespace LatticeSystem.Tests.SpinHalfFamily

open LatticeSystem.Quantum

/-! ## D. signature shims for `spinHalfOp{1,2,3}` -/

example : spinHalfOp1.IsHermitian := spinHalfOp1_isHermitian
example : spinHalfOp2.IsHermitian := spinHalfOp2_isHermitian
example : spinHalfOp3.IsHermitian := spinHalfOp3_isHermitian

example : spinHalfOp1 * spinHalfOp1 = (1 / 4 : ℂ) • 1 :=
  spinHalfOp1_mul_self

example : spinHalfOp2 * spinHalfOp2 = (1 / 4 : ℂ) • 1 :=
  spinHalfOp2_mul_self

example : spinHalfOp3 * spinHalfOp3 = (1 / 4 : ℂ) • 1 :=
  spinHalfOp3_mul_self

/-! ## D. raising/lowering bridges (Tasaki §2.1 (2.1.4)) -/

example :
    spinHalfOpPlus = spinHalfOp1 + Complex.I • spinHalfOp2 :=
  spinHalfOpPlus_eq_add

example :
    spinHalfOpMinus = spinHalfOp1 - Complex.I • spinHalfOp2 :=
  spinHalfOpMinus_eq_sub

/-! ## D. ladder action on basis vectors -/

example : spinHalfOpMinus.mulVec spinHalfUp = spinHalfDown :=
  spinHalfOpMinus_mulVec_spinHalfUp

example : spinHalfOpPlus.mulVec spinHalfDown = spinHalfUp :=
  spinHalfOpPlus_mulVec_spinHalfDown

/-! ## A + B. matrix entry-wise on `Fin 2 × Fin 2` -/

/-- `spinHalfOp3` diagonal: `(1/2, -1/2)`. -/
example :
    spinHalfOp3 = !![(1 / 2 : ℂ), 0; 0, -(1 / 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp3, pauliZ]

/-- `spinHalfOp1` is real symmetric `((0, 1/2); (1/2, 0))`. -/
example :
    spinHalfOp1 = !![0, (1 / 2 : ℂ); (1 / 2 : ℂ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp1, pauliX]

/-! ## G. small exhaustive on `Fin 2`: ladder operators in matrix
form -/

example : spinHalfOpPlus = !![0, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOp1, spinHalfOp2, pauliX, pauliY]

example : spinHalfOpMinus = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpMinus, spinHalfOp1, spinHalfOp2, pauliX, pauliY]

end LatticeSystem.Tests.SpinHalfFamily
