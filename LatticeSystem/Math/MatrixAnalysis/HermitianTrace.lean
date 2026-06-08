import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
# Reality of traces involving Hermitian matrices

Small generic linear-algebra facts about traces of (products of) Hermitian complex matrices,
extracted from the physics file `Quantum/GibbsState.lean` where they were the algebraic core of the
reality of the partition function and Gibbs expectations:

* `Matrix.IsHermitian.trace_im` — the trace of a Hermitian matrix is real.
* `Matrix.trace_mul_star_of_isHermitian` — `Tr(A · B)` of two Hermitian matrices is invariant under
  complex conjugation (using the cyclic property `Matrix.trace_mul_comm`).

Both are independent of the Gibbs construction; they belong in the generic matrix-analysis layer.
-/

namespace Matrix

variable {n : Type*} [Fintype n]

/-- For any Hermitian matrix `A : Matrix n n ℂ`, the trace is real. -/
theorem IsHermitian.trace_im {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.im = 0 := by
  have : star A.trace = A.trace := by
    rw [← Matrix.trace_conjTranspose, hA.eq]
  exact Complex.conj_eq_iff_im.mp this

/-- For Hermitian matrices `A`, `B` over `ℂ`, the trace `Tr(A · B)` is invariant under complex
conjugation.  This is the algebraic core of the reality of Gibbs expectations and is independent of
the Gibbs construction. -/
theorem trace_mul_star_of_isHermitian {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    star (A * B).trace = (A * B).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hA.eq,
    Matrix.trace_mul_comm]

end Matrix
