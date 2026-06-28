/-
The square-root form of the reflection-positivity Cauchy–Schwarz inequality
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 40).

Taking square roots in the chessboard inequality `(Re Tr(M·θA·B))² ≤ Re Tr(M·θA·A)·Re Tr(M·θB·B)`
gives the usable Cauchy–Schwarz bound
`|Re Tr(M·θA·B)| ≤ √(Re Tr(M·θA·A)) · √(Re Tr(M·θB·B))`,
valid for a reflection-invariant reflection-positive trace weight `M` and left-supported `A`, `B`
(the diagonals are nonnegative because `M` is reflection-positive).  This is the form iterated in
the Dyson–Lieb–Simon spreading argument toward Gaussian domination.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionChessboard
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Square-root reflection-positivity Cauchy–Schwarz.**  For a reflection-invariant
reflection-positive trace weight `M` and left-supported `A`, `B`,
`|Re Tr(M·θA·B)| ≤ √(Re Tr(M·θA·A)) · √(Re Tr(M·θB·B))`. -/
theorem rpTraceWeight_cauchySchwarz_abs {M A B : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hθM : ringReflectionThetaS n N M = M)
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    |(M * (ringReflectionThetaS n N A * B)).trace.re|
      ≤ Real.sqrt (M * (ringReflectionThetaS n N A * A)).trace.re
        * Real.sqrt (M * (ringReflectionThetaS n N B * B)).trace.re := by
  have hchess := rpTraceWeight_reflection_step hM hθM hA hB
  calc |(M * (ringReflectionThetaS n N A * B)).trace.re|
      = Real.sqrt ((M * (ringReflectionThetaS n N A * B)).trace.re ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((M * (ringReflectionThetaS n N A * A)).trace.re
          * (M * (ringReflectionThetaS n N B * B)).trace.re) := Real.sqrt_le_sqrt hchess
    _ = Real.sqrt (M * (ringReflectionThetaS n N A * A)).trace.re
          * Real.sqrt (M * (ringReflectionThetaS n N B * B)).trace.re :=
        Real.sqrt_mul (hM A hA) _

end LatticeSystem.Quantum
