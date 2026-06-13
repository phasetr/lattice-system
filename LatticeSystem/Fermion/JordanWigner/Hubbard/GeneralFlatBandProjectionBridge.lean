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

end LatticeSystem.Fermion
