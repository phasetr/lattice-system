/-
The reflection-positivity chessboard inequality
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 34).

For a reflection-invariant reflection-positive trace weight `M` (`θ M = M`) and left-supported
`A`, `B`, the off-diagonal value of the reflection-positivity form is symmetric,
`Re Tr(M·θA·B) = Re Tr(M·θB·A)` (because `A` commutes with `θB`, which lives on the right half).
Feeding this symmetry into the Cauchy–Schwarz discriminant inequality collapses the cross term and
gives the chessboard bound `(Re Tr(M·θA·B))² ≤ Re Tr(M·θA·A) · Re Tr(M·θB·B)` — the Dyson–Lieb–Simon
factorization step underlying Gaussian domination.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTraceReality

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Symmetry of the reflection-positivity form.**  For a reflection-invariant weight `M`
(`θ M = M`) and left-supported `A`, `B`, the off-diagonal value is symmetric:
`Re Tr(M·θA·B) = Re Tr(M·θB·A)`.  Indeed `conj Tr(M·θA·B) = Tr(M·θB·A)` (`θ`-trace identity, `θ`
multiplicativity, `θ² = id`, `θ M = M`, and `A` commutes with `θB`), and conjugation fixes the real
part. -/
theorem rpForm_re_symm {M A B : ManyBodyOpS (Fin (2 * n)) N}
    (hθM : ringReflectionThetaS n N M = M) (hA : SupportedOnLeftS n N A)
    (hB : SupportedOnLeftS n N B) :
    (M * (ringReflectionThetaS n N A * B)).trace.re
      = (M * (ringReflectionThetaS n N B * A)).trace.re := by
  have hconj : starRingEnd ℂ ((M * (ringReflectionThetaS n N A * B)).trace)
      = (M * (ringReflectionThetaS n N B * A)).trace := by
    rw [← ringReflectionThetaS_trace]
    congr 1
    rw [ringReflectionThetaS_mul, ringReflectionThetaS_mul, ringReflectionThetaS_involutive n N A,
      hθM, hA.mul_theta_comm hB]
  rw [← hconj, Complex.conj_re]

/-- **Reflection-positivity chessboard inequality.**  For a reflection-invariant reflection-positive
trace weight `M` and left-supported `A`, `B`,
`(Re Tr(M·θA·B))² ≤ Re Tr(M·θA·A) · Re Tr(M·θB·B)`.  The Dyson–Lieb–Simon factorization step. -/
theorem rpTraceWeight_reflection_step {M A B : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hθM : ringReflectionThetaS n N M = M)
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    ((M * (ringReflectionThetaS n N A * B)).trace.re) ^ 2
      ≤ (M * (ringReflectionThetaS n N A * A)).trace.re
        * (M * (ringReflectionThetaS n N B * B)).trace.re := by
  have hcs := rpTraceWeight_cauchySchwarz hM hA hB
  have hsymm := rpForm_re_symm hθM hA hB
  rw [hsymm] at hcs ⊢
  nlinarith [hcs]

end LatticeSystem.Quantum
