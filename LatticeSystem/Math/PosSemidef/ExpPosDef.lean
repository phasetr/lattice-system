import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Positive-definiteness of the matrix exponential of a Hermitian matrix

Generic finite-dimensional linear algebra.  For a Hermitian complex matrix `A`, the matrix
exponential `exp A` is positive definite.

The proof avoids the continuous-functional-calculus route (which causes deterministic
typeclass-resolution timeouts, see `LatticeSystem.Quantum.GibbsState`).  Instead it uses the
algebraic square-root split: writing `M = exp(A/2)` — which is Hermitian because `A/2` is
(`Matrix.IsHermitian.exp`) and invertible because every matrix exponential is a unit
(`Matrix.isUnit_exp`) — the commuting-exponent addition law `exp(A/2 + A/2) = M · M`
(`Matrix.exp_add_of_commute`) gives `exp A = Mᴴ · M`, which is positive definite by
`Matrix.PosDef.conjTranspose_mul_self` (using injectivity of `M.mulVec` from invertibility).

This is the load-bearing strict positivity behind Gibbs partition functions
`Z_β(H) = Tr exp(−βH) > 0` for Hermitian Hamiltonians `H` (needed as the domain condition of the
`−log Z` symmetrisation step in Tasaki §4.1 Theorem 4.2, reflection-positivity layer).
-/

namespace Matrix

open NormedSpace
open scoped ComplexOrder

/-- **The exponential of a Hermitian matrix is positive definite.**  For a Hermitian complex matrix
`A`, `exp A` is positive definite: with `M = exp(A/2)` Hermitian (`Matrix.IsHermitian.exp`) and
invertible (`Matrix.isUnit_exp`), the commuting split `exp A = M · M = Mᴴ · M` is positive definite
by `Matrix.PosDef.conjTranspose_mul_self`.  Generic ingredient for the strict positivity of Gibbs
partition functions `Tr exp(−βH) > 0` (Tasaki §4.1, reflection-positivity layer). -/
theorem posDef_exp_of_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) : (NormedSpace.exp A).PosDef := by
  have hsa : IsSelfAdjoint (2⁻¹ : ℂ) := by rw [isSelfAdjoint_iff, star_inv₀, star_ofNat]
  have hMHerm : (NormedSpace.exp ((2⁻¹ : ℂ) • A)).IsHermitian := (hA.smul hsa).exp
  have hinj : Function.Injective (NormedSpace.exp ((2⁻¹ : ℂ) • A)).mulVec :=
    Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _)
  have hsplit : NormedSpace.exp A
      = (NormedSpace.exp ((2⁻¹ : ℂ) • A))ᴴ * NormedSpace.exp ((2⁻¹ : ℂ) • A) := by
    rw [hMHerm.eq, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul,
      show (2⁻¹ + 2⁻¹ : ℂ) = 1 by norm_num, one_smul]
  rw [hsplit]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end Matrix
