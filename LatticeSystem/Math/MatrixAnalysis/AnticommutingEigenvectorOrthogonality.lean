import Mathlib.Data.Matrix.Mul
import LatticeSystem.Math.ComplexVectorKernel

/-!
# Orthogonality forced by an anticommuting isometry

A generic finite-dimensional linear-algebra fact, free of any lattice or spin content: if `U` is an
isometry (`Uᴴ U = 1`), `V` anticommutes with `U`, and `Φ ≠ 0` is an eigenvector of `U`, then `Φ` is
orthogonal to `V Φ`.

The mechanism is a two-line phase argument.  Conjugating by `U` leaves the overlap
`z = ⟪Φ, V Φ⟫` unchanged, because the eigenvalue `λ` of a unitary eigenvector satisfies
`λ̄ λ = 1`; but `Uᴴ V U = −V` by the anticommutation, so the same conjugation also sends `z` to
`−z`.  Hence `z = −z` and `z = 0`.

`Φ ≠ 0` is an explicit hypothesis: it is what "eigenvector" means, and it is what makes
`λ̄ λ = 1` derivable (the self inner product may then be cancelled).
-/

namespace Matrix

open LatticeSystem

/-- **Orthogonality from an anticommuting isometry.**  If `Uᴴ U = 1`, if `V U = −(U V)`, and if
`Φ ≠ 0` satisfies `U Φ = λ Φ`, then `⟪Φ, V Φ⟫ = 0`.  Neither `[Nonempty n]` nor a separate
`λ ≠ 0` hypothesis is needed: `λ̄ λ = 1` follows from the isometry property. -/
theorem dotProduct_mulVec_eq_zero_of_anticommute_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n] {U V : Matrix n n ℂ}
    (hU : U.conjTranspose * U = 1) (hanti : V * U = -(U * V))
    {Φ : n → ℂ} (hΦ : Φ ≠ 0) {lam : ℂ} (heig : U.mulVec Φ = lam • Φ) :
    star Φ ⬝ᵥ V.mulVec Φ = 0 := by
  have hpos : star Φ ⬝ᵥ Φ ≠ 0 := by
    intro h
    have hre := dotProduct_star_self_re_pos hΦ
    rw [h] at hre
    simp at hre
  have hcc : star lam * lam = 1 := by
    have hu : star (U.mulVec Φ) ⬝ᵥ U.mulVec Φ = star Φ ⬝ᵥ Φ := by
      rw [star_mulVec_dotProduct, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    rw [heig, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc] at hu
    exact mul_right_cancel₀ hpos (hu.trans (one_mul _).symm)
  have hconj : star Φ ⬝ᵥ (U.conjTranspose * V * U).mulVec Φ = star Φ ⬝ᵥ V.mulVec Φ := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← star_mulVec_dotProduct, heig,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, star_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc, one_mul]
  have hneg : U.conjTranspose * V * U = -V := by
    rw [Matrix.mul_assoc, hanti, Matrix.mul_neg, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [hneg, Matrix.neg_mulVec, dotProduct_neg] at hconj
  linear_combination (-1 / 2 : ℂ) * hconj

end Matrix
