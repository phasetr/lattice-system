import Mathlib.Analysis.Matrix.Order
import LatticeSystem.Math.MatrixAnalysis.CourantFischer

/-!
# Tasaki Appendix A.2.3: eigenvalue monotonicity (Theorem A.7)

Tasaki's Theorem A.7 (the min–max / Courant–Fischer monotonicity, "relatively unknown to
physicists but important"): if self-adjoint operators satisfy `Â ≤ B̂`, then the `j`-th
eigenvalue of `Â` is at most the `j`-th eigenvalue of `B̂` (eigenvalues ordered).  The proof is
the min–max principle (eq. (A.2.30)),
`a_j = min_{dim M = j} max_{Φ ∈ M, ‖Φ‖=1} ⟨Φ|Â|Φ⟩`,
together with `⟨Φ|Â|Φ⟩ ≤ ⟨Φ|B̂|Φ⟩`.

We state it for finite complex matrices using mathlib's *sorted* eigenvalue function
`Matrix.IsHermitian.eigenvalues₀ : Fin (card n) → ℝ` (antitone — largest first).  With this
indexing `∀ i, (eigenvalues₀ of A) i ≤ (eigenvalues₀ of B) i` says "the `i`-th largest
eigenvalue is monotone in the Loewner order `≤`", which is exactly Tasaki's `a_j ≤ b_j`
(re-indexed from smallest-first to largest-first).  mathlib has the variational principle for
the extreme eigenvalues but not the general min–max monotonicity for matrices; the missing
Courant–Fischer block/pigeonhole machinery is built in `CourantFischer.lean`, and this theorem is
**now proved (axiom-free)** from it (`LatticeSystem.Quantum.hermitian_eigenvalues₀_mono`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Theorem A.7 and eq. (A.2.30), p. 468.
-/

namespace LatticeSystem.Math

open Matrix
open scoped MatrixOrder ComplexOrder

/-- **Tasaki Theorem A.7 (eigenvalue monotonicity / min–max).**  For Hermitian matrices
`A ≤ B` (the Loewner order, `B - A` positive-semidefinite), every sorted eigenvalue of `A` is
at most the corresponding sorted eigenvalue of `B`: `∀ i, A.eigenvalues₀ i ≤ B.eigenvalues₀ i`
(eigenvalues largest-first).  **Now proved (axiom-free)** via the Courant–Fischer block/pigeonhole
argument (`LatticeSystem.Quantum.hermitian_eigenvalues₀_mono`, `CourantFischer.lean`): the top
`(i+1)`-eigenspace of `A` and the bottom `(card n − i)`-eigenspace of `B` have dimensions summing to
`card n + 1`, so they meet in a nonzero `x`; the block Rayleigh bounds + Loewner monotonicity give
`A.eigenvalues₀ i · ‖x‖² ≤ ⟨x,Ax⟩ ≤ ⟨x,Bx⟩ ≤ B.eigenvalues₀ i · ‖x‖²`. -/
theorem hermitian_eigenvalues₀_monotone {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B) :
    ∀ i : Fin (Fintype.card n), hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i :=
  fun i => LatticeSystem.Quantum.hermitian_eigenvalues₀_mono hA hB hAB i

end LatticeSystem.Math
