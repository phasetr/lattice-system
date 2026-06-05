import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Tasaki Appendix A.2.3: monotonicity of the trace of the exponential (Corollary A.8)

Corollary of the eigenvalue monotonicity (Theorem A.7), "useful in quantum statistical
mechanics": if self-adjoint operators satisfy `Â ≤ B̂`, then
`Tr[e^Â] ≤ Tr[e^B̂]`  (Tasaki eq. (A.2.31)),
and more generally `Tr[f(Â)] ≤ Tr[f(B̂)]` for any non-decreasing `f : ℝ → ℝ` (eq. (A.2.32)).
The proof is immediate from Theorem A.7: with the eigenvalues ordered, `a_j ≤ b_j`, so
`Σ_j f(a_j) ≤ Σ_j f(b_j)` for monotone `f`, and `Tr[f(Â)] = Σ_j f(a_j)`.

We record the concrete `f = exp` form (eq. (A.2.31)) for finite complex matrices.  Since it
rests on Theorem A.7 (itself a documented axiom here) and on the spectral mapping
`eigenvalues(e^Â) = e^{eigenvalues(Â)}`, it is recorded as a documented axiom (to be discharged
together with A.7); the general monotone-`f` form (eq. (A.2.32)) holds the same way.  `Tr` of a
self-adjoint matrix is real, so the comparison is of real parts.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Corollary A.8, eqs. (A.2.31)–(A.2.32), p. 468.
-/

namespace LatticeSystem.Math

open Matrix
open scoped MatrixOrder ComplexOrder

/-- **Tasaki Corollary A.8 (trace of the exponential is monotone), AXIOM.**  For Hermitian
matrices `A ≤ B` (the Loewner order), `Tr[e^A] ≤ Tr[e^B]` (Tasaki eq. (A.2.31)).  Immediate from
the eigenvalue monotonicity (Theorem A.7) via `Tr[e^A] = Σ_j e^{a_j}` and `a_j ≤ b_j`; recorded
as a documented axiom (resting on the axiom A.7 and the spectral mapping for `exp`).  The
general form `Tr[f(A)] ≤ Tr[f(B)]` for non-decreasing `f` (eq. (A.2.32)) holds the same way. -/
axiom hermitian_trace_exp_monotone {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B) :
    (NormedSpace.exp A).trace.re ≤ (NormedSpace.exp B).trace.re

end LatticeSystem.Math
