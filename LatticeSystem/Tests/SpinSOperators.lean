import LatticeSystem.Quantum.SpinS.Operators

/-!
# Test coverage for the spin-`S` operators (Tasaki §2.1 P1d''' / β-1)
-/

namespace LatticeSystem.Tests.SpinSOperators

open LatticeSystem.Quantum

/-- Diagonal entries of `Ŝ^{(3)}` are the magnetic quantum numbers. -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSOp3 N k k = (N : ℂ) / 2 - (k.val : ℂ) :=
  spinSOp3_apply_diag N k

/-- For `N = 1` (S = 1/2), the eigenvalues of `Ŝ^{(3)}` at indices 0, 1
are `+1/2` and `-1/2`. -/
example : spinSOp3 1 ⟨0, by decide⟩ ⟨0, by decide⟩ = (1 / 2 : ℂ) := by
  rw [spinSOp3_apply_diag]; norm_num

example : spinSOp3 1 ⟨1, by decide⟩ ⟨1, by decide⟩ = -(1 / 2 : ℂ) := by
  rw [spinSOp3_apply_diag]; norm_num

/-- For `N = 2` (S = 1), the eigenvalues at indices 0, 1, 2 are
`+1, 0, -1`. -/
example : spinSOp3 2 ⟨0, by decide⟩ ⟨0, by decide⟩ = (1 : ℂ) := by
  rw [spinSOp3_apply_diag]; norm_num

example : spinSOp3 2 ⟨1, by decide⟩ ⟨1, by decide⟩ = (0 : ℂ) := by
  rw [spinSOp3_apply_diag]; norm_num

example : spinSOp3 2 ⟨2, by decide⟩ ⟨2, by decide⟩ = -(1 : ℂ) := by
  rw [spinSOp3_apply_diag]; norm_num

/-- `Ŝ^+` annihilates the highest-weight state (top of ladder). -/
example (N : ℕ) (j : Fin (N + 1)) :
    spinSOpPlus N (Fin.last N) j = 0 :=
  spinSOpPlus_apply_top N j

/-- `Ŝ^-` annihilates the lowest-weight state (bottom of ladder). -/
example (N : ℕ) (j : Fin (N + 1)) :
    spinSOpMinus N ⟨0, Nat.succ_pos N⟩ j = 0 :=
  spinSOpMinus_apply_bottom N j

end LatticeSystem.Tests.SpinSOperators
