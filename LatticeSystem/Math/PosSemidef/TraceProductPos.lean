import Mathlib.Analysis.Matrix.PosDef

/-!
# Positivity of the trace of a product of positive-definite matrices

Generic finite-dimensional linear algebra.  For two positive-definite complex matrices `A` and
`B` (over a nonempty index type), the trace of the product is strictly positive (as a complex
number, under the `ComplexOrder` order in which `0 < z ↔ 0 < z.re ∧ z.im = 0`):
`0 < Tr(A · B)`.

The proof diagonalizes `B` by the spectral theorem (`Matrix.IsHermitian.spectral_theorem`),
`B = U · diag(λ) · Uᴴ` with `U` unitary and eigenvalues `λ_i > 0`
(`Matrix.PosDef.eigenvalues_pos`).  Cycling the trace (`Matrix.trace_mul_cycle`) gives
`Tr(A · B) = Tr((Uᴴ · A · U) · diag(λ)) = Σ_i (Uᴴ · A · U)_{ii} · λ_i`, where each diagonal
entry `(Uᴴ · A · U)_{ii}` is positive because `Uᴴ · A · U` is again positive definite
(`Matrix.PosDef.conjTranspose_mul_mul_same`, using that a unitary matrix has injective `mulVec`)
and hence has positive diagonal (`Matrix.PosDef.diag_pos`).  A sum of positive terms over a
nonempty index set is positive (`Finset.sum_pos`).

This is the generic step behind the non-orthogonality (`Tr(W'W) > 0`) argument in the
uniqueness proof of Tasaki §10.2.4 (Lieb's theorem for the attractive Hubbard model, Issue #4852).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.),
§10.2.4, p. 372.
-/

namespace Matrix.PosDef

open Matrix
open scoped ComplexOrder

/-- **The trace of a product of two positive-definite matrices is strictly positive.**
For positive-definite complex matrices `A`, `B` over a nonempty (finite, decidable) index type,
`0 < Tr(A · B)` in the `ComplexOrder`.  The trace is real and positive: diagonalizing `B` as
`U · diag(λ) · Uᴴ` and cycling the trace expresses `Tr(A · B) = Σ_i (Uᴴ · A · U)_{ii} · λ_i`, a
sum of products of positive reals (positive diagonal of the positive-definite `Uᴴ · A · U`, times
positive eigenvalues of `B`).  Generic ingredient for the `Tr(W'W) > 0` non-orthogonality step of
Tasaki §10.2.4. -/
theorem trace_mul_pos {n : Type*} [Fintype n] [Nonempty n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    0 < (A * B).trace := by
  classical
  have hBH : B.IsHermitian := hB.isHermitian
  have hu : IsUnit (hBH.eigenvectorUnitary : Matrix n n ℂ) :=
    IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self hBH.eigenvectorUnitary)
  have hUinj : Function.Injective (hBH.eigenvectorUnitary : Matrix n n ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hu
  have hS : ((hBH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A *
      (hBH.eigenvectorUnitary : Matrix n n ℂ)).PosDef :=
    hA.conjTranspose_mul_mul_same hUinj
  have key : (A * B).trace
      = ((hBH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A *
          (hBH.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hBH.eigenvalues)).trace := by
    conv_lhs =>
      rw [hBH.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  rw [key]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Function.comp_apply]
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  exact mul_pos hS.diag_pos (RCLike.ofReal_pos.mpr (hB.eigenvalues_pos i))

end Matrix.PosDef
