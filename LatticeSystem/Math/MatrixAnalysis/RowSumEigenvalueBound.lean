import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Eigenvalue bounds from a uniform row-sum bound

Gershgorin's circle theorem places every eigenvalue of a square matrix in a disc centred at some
diagonal entry `t k k` with radius `∑_{j ≠ k} ‖t k j‖`.  Adding the centre back to the radius turns
that statement into the `ℓ^∞`-operator-norm estimate recorded here: a uniform bound `K` on the row
sums `∑_j ‖t x j‖` bounds every eigenvalue in modulus by `K`.

Two forms are provided: one for an arbitrary eigenpair given by the matrix–vector equation, and one
for the eigenvalues of a Hermitian matrix, stated with the real absolute value so that a consumer
obtains the two-sided bound `-K ≤ ε_j ≤ K` by `abs_le`.
-/

namespace LatticeSystem.Math

open Matrix

/-- **An eigenvalue is bounded by the row sums**: if `t·w = λ w` for some `w ≠ 0` and every row of
`t` satisfies `∑_j ‖t x j‖ ≤ K`, then `‖λ‖ ≤ K`.  Gershgorin's circle theorem puts `λ` within
`∑_{j ≠ k} ‖t k j‖` of the diagonal entry `t k k` for some index `k`; the triangle inequality then
bounds `‖λ‖` by the full `k`-th row sum. -/
theorem norm_le_of_mulVec_eq_smul_of_rowSum_le {n : Type*} [Fintype n]
    {t : Matrix n n ℂ} {lam : ℂ} {w : n → ℂ} (hw : w ≠ 0) (heig : t.mulVec w = lam • w)
    {K : ℝ} (hK : ∀ x, ∑ y, ‖t x y‖ ≤ K) :
    ‖lam‖ ≤ K := by
  classical
  have hhas : Module.End.HasEigenvalue (Matrix.toLin' t) lam := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
    refine ⟨?_, hw⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, heig]
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hhas
  rw [Metric.mem_closedBall, Complex.dist_eq] at hk
  have h1 : ‖lam‖ ≤ ‖t k k‖ + ∑ j ∈ Finset.univ.erase k, ‖t k j‖ := by
    have := norm_sub_norm_le lam (t k k)
    have h2 : ‖lam - t k k‖ ≤ ∑ j ∈ Finset.univ.erase k, ‖t k j‖ := hk
    linarith
  have h3 : ‖t k k‖ + ∑ j ∈ Finset.univ.erase k, ‖t k j‖ = ∑ j, ‖t k j‖ :=
    Finset.add_sum_erase Finset.univ (fun j => ‖t k j‖) (Finset.mem_univ k)
  linarith [hK k, h3 ▸ h1]

/-- **The eigenvalues of a Hermitian matrix are bounded by its row sums**: `|ε_j| ≤ K` whenever
every row satisfies `∑_y ‖t x y‖ ≤ K`.  The eigenvector basis supplies the eigenpair consumed by
`norm_le_of_mulVec_eq_smul_of_rowSum_le`; the real absolute value is the form from which `abs_le`
delivers the two-sided bound `-K ≤ ε_j ≤ K`. -/
theorem abs_eigenvalues_le_of_rowSum_le {n : Type*} [Fintype n] [DecidableEq n]
    {t : Matrix n n ℂ} (hT : t.IsHermitian) {K : ℝ} (hK : ∀ x, ∑ y, ‖t x y‖ ≤ K) (j : n) :
    |hT.eigenvalues j| ≤ K := by
  have hw : (⇑(hT.eigenvectorBasis j) : n → ℂ) ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 (hT.eigenvectorBasis.orthonormal.ne_zero j)
  have heig : t.mulVec (⇑(hT.eigenvectorBasis j) : n → ℂ)
      = ((hT.eigenvalues j : ℝ) : ℂ) • (⇑(hT.eigenvectorBasis j) : n → ℂ) := by
    rw [hT.mulVec_eigenvectorBasis]
    funext i
    simp [Complex.real_smul]
  have h := norm_le_of_mulVec_eq_smul_of_rowSum_le hw heig hK
  rwa [Complex.norm_real, Real.norm_eq_abs] at h

end LatticeSystem.Math
