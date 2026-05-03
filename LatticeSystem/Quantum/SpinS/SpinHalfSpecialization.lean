import LatticeSystem.Quantum.SpinS.Operators
import LatticeSystem.Quantum.SpinHalfBasis

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

end LatticeSystem.Quantum
