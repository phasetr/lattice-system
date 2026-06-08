import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Tasaki Appendix A.2.2: the Lie product formula (Theorem A.1)

The first numbered result of Tasaki's Mathematical Appendix.  For any (bounded) operators
`Â`, `B̂` — here finite complex matrices `Matrix n n ℂ`, the operator algebra of a
finite-volume quantum system — the exponential of a sum is the limit of symmetrically split
products:
`e^{Â+B̂} = lim_{N↑∞} (e^{Â/N} e^{B̂/N})^N`  (Tasaki eq. (A.2.21)).
Mathlib provides the *commuting* case (`Matrix.exp_add_of_commute`); the general
non-commuting Lie/Trotter formula for bounded operators is a standard but non-trivial
real-analysis result (Tasaki's footnote: "nineteenth century mathematics"), not currently in
mathlib.  Per the project's axiomatize-first policy it is recorded here as a documented axiom,
to be discharged later; it is not on the critical path of any Chapter-11 proof.

`NormedSpace.exp` is the matrix exponential used throughout the project (e.g. the Gibbs
exponential `e^{-βH}`); `(N : ℂ)⁻¹ • A = A/N`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.2, Theorem A.1, eq. (A.2.21), p. 465.
-/

namespace LatticeSystem.Math

open Filter Topology

/-- **Tasaki Theorem A.1 (Lie product formula), AXIOM.**  For finite complex matrices `A`, `B`,
the exponential of the sum is the limit of the symmetric split product,
`e^{A+B} = lim_{N↑∞} (e^{A/N} e^{B/N})^N`.  Specializes to `Matrix.exp_add_of_commute` when
`A`, `B` commute; the general case is recorded as a documented axiom (standard analysis,
deferred). -/
axiom lieProductFormula {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    Tendsto
      (fun N : ℕ => (NormedSpace.exp ((N : ℂ)⁻¹ • A) * NormedSpace.exp ((N : ℂ)⁻¹ • B)) ^ N)
      atTop (𝓝 (NormedSpace.exp (A + B)))

end LatticeSystem.Math
