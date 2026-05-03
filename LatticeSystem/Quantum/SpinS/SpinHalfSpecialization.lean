import LatticeSystem.Quantum.SpinS.Operators
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.Pauli

/-!
# Spin-`S` specialisation at `N = 1`: equals spin-`1/2`

For `N = 1` (i.e., `S = 1/2`), the spin-`S` operators
`spinSOp{Plus, Minus}` coincide with the standard spin-`1/2`
operators `spinHalfOp{Plus, Minus}`.

These specialisation identities provide a bridge between the
generic spin-`S` formalism and the spin-`1/2` infrastructure,
useful for transferring results in either direction.

Tracked as part of Tasaki §2.1 / §2.4 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

/-- `spinSOpPlus 1 = spinHalfOpPlus`: the spin-`S` raising operator
at `N = 1` is the standard spin-`1/2` raising matrix `!![0,1;0,0]`. -/
theorem spinSOpPlus_one_eq_spinHalfOpPlus :
    spinSOpPlus 1 = spinHalfOpPlus := by
  unfold spinSOpPlus spinHalfOpPlus
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- `spinSOpMinus 1 = spinHalfOpMinus`: the spin-`S` lowering
operator at `N = 1` is the standard spin-`1/2` lowering matrix
`!![0,0;1,0]`. -/
theorem spinSOpMinus_one_eq_spinHalfOpMinus :
    spinSOpMinus 1 = spinHalfOpMinus := by
  unfold spinSOpMinus spinHalfOpMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- `spinSOp3 1 = spinHalfOp3`: the spin-`S` `Ŝ^{(3)}` operator at
`N = 1` is the standard spin-`1/2` operator `(1/2) • σ^z`. -/
theorem spinSOp3_one_eq_spinHalfOp3 :
    spinSOp3 1 = spinHalfOp3 := by
  unfold spinSOp3 spinHalfOp3 pauliZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- `spinSOp1 1 = spinHalfOp1`: the spin-`S` `Ŝ^{(1)}` operator at
`N = 1` is the standard spin-`1/2` operator `(1/2) • σ^x`. -/
theorem spinSOp1_one_eq_spinHalfOp1 :
    spinSOp1 1 = spinHalfOp1 := by
  unfold spinSOp1 spinHalfOp1 pauliX
  rw [spinSOpPlus_one_eq_spinHalfOpPlus, spinSOpMinus_one_eq_spinHalfOpMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinHalfOpPlus, spinHalfOpMinus]

/-- `spinSOp2 1 = spinHalfOp2`: the spin-`S` `Ŝ^{(2)}` operator at
`N = 1` is the standard spin-`1/2` operator `(1/2) • σ^y`. -/
theorem spinSOp2_one_eq_spinHalfOp2 :
    spinSOp2 1 = spinHalfOp2 := by
  unfold spinSOp2 spinHalfOp2 pauliY
  rw [spinSOpPlus_one_eq_spinHalfOpPlus, spinSOpMinus_one_eq_spinHalfOpMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfOpPlus, spinHalfOpMinus, Complex.ext_iff] <;>
    field_simp <;> ring

end LatticeSystem.Quantum
