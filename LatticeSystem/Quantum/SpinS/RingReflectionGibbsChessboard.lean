/-
The reflection-positivity chessboard inequality for the concrete gauged ring Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 36).

The gauged ring Gibbs weight `exp(−β · ringDLSDecomposition.toHamiltonian)` is both a
reflection-positive trace weight (the Gibbs capstone) and reflection-invariant (`θ M = M`).  Feeding
these two facts into the abstract chessboard inequality gives the concrete Dyson–Lieb–Simon
factorization estimate for the thermal state of the physical ring antiferromagnet: for
left-supported `A`, `B` and `β ≥ 0`,
`(Re Tr(M·θA·B))² ≤ Re Tr(M·θA·A) · Re Tr(M·θB·B)` with `M = exp(−β · toHamiltonian)`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionThetaInvariance

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Chessboard inequality for the gauged ring Gibbs weight.**  For `β ≥ 0` and left-supported
`A`, `B`, with `M = exp(−β · toHamiltonian)` the reflection-positive Gibbs weight of the gauged ring
antiferromagnet, `(Re Tr(M·θA·B))² ≤ Re Tr(M·θA·A) · Re Tr(M·θB·B)`. -/
theorem ringDLSGibbs_reflection_step (n N : ℕ) [NeZero n] {β : ℝ} (hβ : 0 ≤ β)
    {A B : ManyBodyOpS (Fin (2 * n)) N} (hA : SupportedOnLeftS n N A)
    (hB : SupportedOnLeftS n N B) :
    ((NormedSpace.exp (-(β : ℂ) • (ringDLSDecomposition n N).toHamiltonian)
        * (ringReflectionThetaS n N A * B)).trace.re) ^ 2
      ≤ (NormedSpace.exp (-(β : ℂ) • (ringDLSDecomposition n N).toHamiltonian)
          * (ringReflectionThetaS n N A * A)).trace.re
        * (NormedSpace.exp (-(β : ℂ) • (ringDLSDecomposition n N).toHamiltonian)
          * (ringReflectionThetaS n N B * B)).trace.re :=
  rpTraceWeight_reflection_step (ringDLSDecomposition_gibbs_rpTraceWeight n N hβ)
    (ringReflectionThetaS_ringDLSGibbs n N β) hA hB

end LatticeSystem.Quantum
