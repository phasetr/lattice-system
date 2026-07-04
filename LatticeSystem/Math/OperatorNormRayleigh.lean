/-
The Rayleigh upper bound by the operator norm: for any complex square matrix `A`, the real part of
the quadratic form `⟨v, A v⟩` is bounded by `‖A‖_op · ‖v‖²`, where `‖A‖_op` is the `L²` operator
norm realized through `Matrix.toEuclideanCLM`.  This is the elementary Cauchy–Schwarz plus
operator-norm estimate `re ⟪x, T x⟫ ≤ ‖x‖ ‖T x‖ ≤ ‖T‖ ‖x‖²`, transported from the abstract
`EuclideanSpace` inner product to the concrete `dotProduct`/`mulVec` calculus on `n → ℂ`.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace LatticeSystem.Math

open Matrix

/-- **Operator-norm Rayleigh bound.**  For a complex square matrix `A` and a vector `v`, the real
part of the quadratic form obeys `Re ⟨v, A v⟩ ≤ ‖A‖_op · Re ⟨v, v⟩`, where `‖A‖_op` is the operator
norm of the associated Euclidean continuous linear map.  Proof: identify `⟨v, A v⟩` with the
`EuclideanSpace` inner product `⟪x, T x⟫` (`T = toEuclideanCLM A`, `x = v`), then chain
`re ⟪x, T x⟫ ≤ ‖x‖ ‖T x‖ ≤ ‖T‖ ‖x‖²` and rewrite `‖x‖² = Re ⟨v, v⟩`. -/
theorem re_dotProduct_mulVec_le_norm_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) :
    (star v ⬝ᵥ A.mulVec v).re
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * (star v ⬝ᵥ v).re := by
  set x : EuclideanSpace ℂ n := WithLp.toLp 2 v with hx
  have hself : ‖x‖ ^ 2 = (star v ⬝ᵥ v).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) x, hx, EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
      RCLike.re_to_complex]
  have hAv : star v ⬝ᵥ A.mulVec v = inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) := by
    rw [hx, toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [hAv, ← hself, ← RCLike.re_to_complex]
  calc RCLike.re (inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) A x))
      ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A x‖ := re_inner_le_norm x _
    _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm x) (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * ‖x‖ ^ 2 := by ring

end LatticeSystem.Math
