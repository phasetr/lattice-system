import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Unitarity of Hermitian-generated matrix exponentials

This file records the adjoint and two-sided unitarity identities for `exp(-iG)` when `G` is
Hermitian.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Adjoint of a Hermitian-generated unitary**: for a Hermitian `G`, the adjoint of `exp(−i G)` is
`exp(+i G)` (`Matrix.exp_conjTranspose` plus `Gᴴ = G`).  The generic fact underlying the LSM twist
operators `Û_LSM = exp(−i G)` and the local twist operators `Û_x = exp(−i M̂_x)`. -/
theorem conjTranspose_exp_neg_I_smul_of_isHermitian {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    (NormedSpace.exp (-Complex.I • G)).conjTranspose = NormedSpace.exp (Complex.I • G) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hG.eq]
  congr 1
  rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]

/-- **A Hermitian-generated exponential is unitary** (`Ûᴴ Û = 1`): for a Hermitian `G`,
`exp(−iG)ᴴ exp(−iG) = exp(iG) exp(−iG) = exp(0) = 1`.  The two exponents commute (both scalar
multiples of `G`), so `Matrix.exp_add_of_commute` collapses the product. -/
theorem conjTranspose_mul_exp_neg_I_smul_of_isHermitian {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    (NormedSpace.exp (-Complex.I • G)).conjTranspose * NormedSpace.exp (-Complex.I • G) = 1 := by
  rw [conjTranspose_exp_neg_I_smul_of_isHermitian hG, ← Matrix.exp_add_of_commute]
  · rw [show Complex.I • G + -Complex.I • G = (0 : Matrix n n ℂ) by rw [neg_smul, add_neg_cancel]]
    exact NormedSpace.exp_zero
  · exact (Commute.refl G).smul_left Complex.I |>.smul_right (-Complex.I)

/-- **A Hermitian-generated exponential is unitary** (`Û Ûᴴ = 1`, companion identity): for a
Hermitian `G`, `exp(−iG) exp(−iG)ᴴ = 1`, by one-sided-inverse commutativity of square matrices. -/
theorem exp_neg_I_smul_mul_conjTranspose_of_isHermitian {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    NormedSpace.exp (-Complex.I • G) * (NormedSpace.exp (-Complex.I • G)).conjTranspose = 1 :=
  mul_eq_one_comm.mpr (conjTranspose_mul_exp_neg_I_smul_of_isHermitian hG)

end LatticeSystem.Quantum
