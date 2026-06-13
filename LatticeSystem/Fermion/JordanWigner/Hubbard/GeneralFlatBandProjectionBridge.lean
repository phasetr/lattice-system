import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBand

/-!
# Flat-band projection matrix P₀: foundations (Tasaki §11.3.4, toward Theorem 11.15)

The orthogonal projection `P₀` onto the flat band `ker T` (`generalFlatBandProjectionMatrix`) is
Hermitian and idempotent, and its entries are inner products `(P₀)_{xy} = ⟪e_x, P₀ e_y⟫`.  These are
the foundations of the bridge
`generalFlatBandProjectionIrreducible T ↔ generalFlatBandBasisConnected I μ` that (composed with the
proved Theorem 11.17) discharges Theorem 11.15.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4, Theorem 11.15, pp. 408-412.  Tracked in Issue #4453.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped ComplexOrder

variable {M : ℕ} (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)

/-- **The projection-matrix entry as an inner product**: `(P₀)_{xy} = ⟪e_x, P₀ e_y⟫`, the
orthonormal-basis matrix element of the orthogonal projection onto `ker T`. -/
theorem generalFlatBandProjectionMatrix_apply (x y : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x y
      = inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)
        ((generalFlatBandKernel T).starProjection
          (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)) := by
  rw [generalFlatBandProjectionMatrix, LinearMap.toMatrixOrthonormal_apply_apply]
  rfl

/-- **`P₀` is Hermitian**: the orthogonal projection onto `ker T` is self-adjoint, so its
orthonormal-basis matrix is Hermitian.  Hence the support matrix `|(P₀)_{xy}|²` is symmetric and its
irreducibility is the strong connectivity of an *undirected* support graph. -/
theorem generalFlatBandProjectionMatrix_isHermitian :
    (generalFlatBandProjectionMatrix T).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply, generalFlatBandProjectionMatrix_apply,
    generalFlatBandProjectionMatrix_apply, ← starRingEnd_apply, inner_conj_symm]
  exact (Submodule.inner_starProjection_left_eq_right (generalFlatBandKernel T) _ _)

/-- **`P₀` is idempotent**: `P₀ · P₀ = P₀` (the matrix of a projection). -/
theorem generalFlatBandProjectionMatrix_isIdempotent :
    generalFlatBandProjectionMatrix T * generalFlatBandProjectionMatrix T
      = generalFlatBandProjectionMatrix T := by
  have h := (generalFlatBandKernel T).isIdempotentElem_starProjection
  unfold generalFlatBandProjectionMatrix
  rw [← map_mul (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin (M + 1)) ℂ))]
  congr 1
  rw [← ContinuousLinearMap.coe_mul, h]

/-- **The diagonal projection density is the squared norm of the projected basis vector**:
`(P₀)_{xx} = ⟪P₀ e_x, P₀ e_x⟫`.  Self-adjointness moves one `P₀` across the inner product and
idempotence merges them, so the diagonal entry equals `‖P₀ e_x‖²`. -/
theorem generalFlatBandProjectionMatrix_diag_eq (x : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x x
      = inner ℂ
          ((generalFlatBandKernel T).starProjection (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x))
          ((generalFlatBandKernel T).starProjection (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)) := by
  rw [generalFlatBandProjectionMatrix_apply]
  conv_lhs => rw [← (generalFlatBandKernel T).isIdempotentElem_starProjection.eq]
  exact (Submodule.inner_starProjection_left_eq_right (generalFlatBandKernel T) _ _).symm

/-- **Active site ⟺ the basis vector is not orthogonal to the flat band**: `(P₀)_{xx} ≠ 0` iff
`P₀ e_x ≠ 0` iff `e_x ∉ (ker T)ᗮ`.  The diagonal density `‖P₀ e_x‖²` is nonzero exactly when the
projection of `e_x` onto the flat band is nonzero. -/
theorem generalFlatBand_diag_ne_zero_iff (x : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x x ≠ 0
      ↔ EuclideanSpace.basisFun (Fin (M + 1)) ℂ x ∉ (generalFlatBandKernel T)ᗮ := by
  rw [generalFlatBandProjectionMatrix_diag_eq, ← Submodule.starProjection_apply_eq_zero_iff,
    ne_eq, not_iff_not, inner_self_eq_zero]

end LatticeSystem.Fermion
