import LatticeSystem.Quantum.SpinS.OffDiagUnit

/-!
# Test coverage for the spin-`S` off-diagonal matrix-unit decomposition
(Tasaki §2.1 P1d''' β-10)
-/

namespace LatticeSystem.Tests.SpinSOffDiagUnit

open LatticeSystem.Quantum

/-- `Ŝ^+ · P_{i+1} = √((i+1)(N − i)) · E_{i, i+1}`. -/
example (N : ℕ) (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    spinSOpPlus N * spinSDiagProj N ⟨i.val + 1, h⟩ =
      Matrix.single i ⟨i.val + 1, h⟩
        ((Real.sqrt (((i.val : ℝ) + 1) * ((N : ℝ) - (i.val : ℝ))) : ℝ) : ℂ) :=
  spinSOpPlus_mul_diagProj_succ_eq_single i h

/-- `Ŝ^- · P_i = √((N − i)(i+1)) · E_{i+1, i}`. -/
example (N : ℕ) (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    spinSOpMinus N * spinSDiagProj N i =
      Matrix.single ⟨i.val + 1, h⟩ i
        ((Real.sqrt (((N : ℝ) - (i.val : ℝ)) * ((i.val : ℝ) + 1)) : ℝ) : ℂ) :=
  spinSOpMinus_mul_diagProj_eq_single i h

end LatticeSystem.Tests.SpinSOffDiagUnit
