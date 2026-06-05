import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Tasaki Appendix A.4.2: polar and singular-value decompositions (Theorems A.19, A.20)

Tasaki's two decomposition theorems for a general square matrix, proved together in the book:

* **Theorem A.19 (polar decomposition)** — any `N × N` matrix `A` factors as `A = W C` with `W`
  unitary and `C` positive-semidefinite (eq. (A.4.2)).
* **Theorem A.20 (singular value decomposition)** — any `N × N` matrix `A` factors as `A = U D V†`
  with `U, V` unitary and `D` a diagonal matrix with nonnegative entries (eqs. (A.4.3)–(A.4.4)); the
  diagonal entries are `√λ_j`, where the `λ_j ≥ 0` are the eigenvalues of the positive-semidefinite
  `A† A` (equivalently `A A†`), eq. (A.4.6).  This underlies the Schmidt decomposition used
  throughout many-body quantum physics.

`mathlib` provides the singular *values* of a linear map
(`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`) but not the constructive matrix-level
factorizations `A = W C` / `A = U D V†`.  In keeping with this project's treatment of other
decomposition/spectral results whose constructive proof is not yet available in `mathlib`
(Theorems A.7, A.8, A.12, and the simultaneous-diagonalization step of A.17), both are recorded as
documented axioms; the statements are kept in book order and the constructive proofs are deferred.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.4.2, Theorems A.19–A.20, eqs. (A.4.2)–(A.4.6), pp. 476–478.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Tasaki Theorem A.19 (polar decomposition), AXIOM.**  Any square complex matrix `A` is written
as `A = W C`, where `W` is unitary (`W ∈ unitaryGroup`) and `C` is positive-semidefinite
(eq. (A.4.2)); for real `A` the unitary `W` can be taken orthogonal.  Recorded as a documented axiom
(the constructive proof — `C = (A† A)^{1/2}` and `W` extending the partial isometry — is not yet
available at the `Matrix` level in `mathlib`). -/
axiom matrix_polar_decomposition (A : Matrix n n ℂ) :
    ∃ (W C : Matrix n n ℂ), W ∈ Matrix.unitaryGroup n ℂ ∧ C.PosSemidef ∧ A = W * C

/-- **Tasaki Theorem A.20 (singular value decomposition), AXIOM.**  Any square complex matrix `A` is
written as `A = U D V†`, where `U` and `V` are unitary and `D = diagonal d` is diagonal with
nonnegative real entries `d_i ≥ 0` (eqs. (A.4.3)–(A.4.4)); the `d_i` are the `√λ_i` with `λ_i ≥ 0`
the eigenvalues of the positive-semidefinite `A† A` (equivalently `A A†`), eq. (A.4.6).  For real
`A` the unitaries `U, V` can be taken orthogonal.  Recorded as a documented axiom (the constructive
factorization is not yet available at the `Matrix` level in `mathlib`). -/
axiom matrix_singular_value_decomposition (A : Matrix n n ℂ) :
    ∃ (U V : Matrix n n ℂ) (d : n → ℝ),
      U ∈ Matrix.unitaryGroup n ℂ ∧ V ∈ Matrix.unitaryGroup n ℂ ∧ (∀ i, 0 ≤ d i) ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Matrix.conjTranspose V

end LatticeSystem.Math
