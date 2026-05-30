import LatticeSystem.Quantum.SpinS.RayleighInfMatrix

/-!
# `BddBelow` for `rayleighOnVec` on the matrix-side unit sphere

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

For a complex matrix `M : Matrix n n ℂ` and a unit vector `v : n → ℂ` (with
`dotProduct (star v) v = 1`), the absolute value of the Rayleigh quotient is
bounded by a concrete sum of matrix entry magnitudes,
`|rayleighOnVec M v| ≤ Σ_{i,j} |M i j|`,
giving `BddBelow` of the Rayleigh range over the matrix-side unit sphere.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [Nonempty n]

/-- For a unit vector `v` (matrix-side: `dotProduct (star v) v = 1`), each component
satisfies `‖v_i‖ ≤ 1`. -/
theorem norm_unit_vec_component_le_one
    {v : n → ℂ} (hunit : dotProduct (star v) v = 1) (i : n) :
    ‖v i‖ ≤ 1 := by
  -- ‖v_i‖² ≤ Σ_j ‖v_j‖² = (dotProduct (star v) v).re = 1.re = 1.
  have hge : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 := by
    refine Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsum : (∑ j, ‖v j‖ ^ 2 : ℝ) = 1 := by
    have : dotProduct (star v) v = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def]
      push_cast
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [this] at hunit
    exact_mod_cast hunit
  have hsq_le : ‖v i‖ ^ 2 ≤ 1 := by rw [← hsum]; exact hge
  nlinarith [sq_nonneg (‖v i‖ - 1), sq_nonneg (‖v i‖ + 1), norm_nonneg (v i)]

end LatticeSystem.Quantum
