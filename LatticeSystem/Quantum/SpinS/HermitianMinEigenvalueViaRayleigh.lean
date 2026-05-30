import LatticeSystem.Quantum.SpinS.RayleighOnEigenvector

/-!
# `hermitianMinEigenvalue` via the Rayleigh quotient

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

For a Hermitian matrix `M : Matrix n n ℂ`, the minimum eigenvalue
`hermitianMinEigenvalue hM` is realised by some index `i₀` of the eigenvalues
array (an index attaining the `Finset.min'` value). This file establishes the
index-existence lemma, the foundation for the Rayleigh-Ritz characterisation
needed by the obligation (2) deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Pick an index `i` whose eigenvalue equals `hermitianMinEigenvalue hM`. -/
theorem exists_index_eigenvalue_eq_hermitianMinEigenvalue
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ i : n, hM.eigenvalues i = hermitianMinEigenvalue hM := by
  have h := hermitian_min_eigenvalue_mem_image hM
  rw [Finset.mem_image] at h
  obtain ⟨i, _, hi⟩ := h
  exact ⟨i, hi⟩

/-- For each index `i`, the unit-eigenvector `(hM.eigenvectorBasis i).ofLp` has
`dotProduct (star v) v = 1`. This is the matrix-side unit normalisation of the
orthonormal eigenvector basis. -/
theorem eigenvectorBasis_dotProduct_self_eq_one
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    dotProduct (star ((hM.eigenvectorBasis i).ofLp))
      ((hM.eigenvectorBasis i).ofLp) = 1 := by
  have hnorm : ‖hM.eigenvectorBasis i‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i
  have hsq : ‖hM.eigenvectorBasis i‖ ^ 2 = 1 := by rw [hnorm]; ring
  rw [EuclideanSpace.norm_sq_eq] at hsq
  -- dotProduct (star v) v = Σ conj(v_i) * v_i = Σ normSq (v_i) = Σ ‖v_i‖² = 1.
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  have hcast : (∑ i_1 : n,
        (starRingEnd ℂ) ((hM.eigenvectorBasis i).ofLp i_1) *
        (hM.eigenvectorBasis i).ofLp i_1 : ℂ) =
      ((∑ i_1 : n, ‖(hM.eigenvectorBasis i).ofLp i_1‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hcast, hsq]
  push_cast
  rfl

/-- **Rayleigh-Ritz existence (lower bound side)**: there exists a unit vector
`v : n → ℂ` (the eigenvector at the minimising eigenvalue index) such that
`rayleighOnVec M v = hermitianMinEigenvalue hM`. -/
theorem exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ v : n → ℂ, dotProduct (star v) v = 1 ∧
      rayleighOnVec M v = hermitianMinEigenvalue hM := by
  obtain ⟨i₀, hi₀⟩ := exists_index_eigenvalue_eq_hermitianMinEigenvalue hM
  refine ⟨(hM.eigenvectorBasis i₀).ofLp, eigenvectorBasis_dotProduct_self_eq_one hM i₀, ?_⟩
  have heig := Matrix.IsHermitian.mulVec_eigenvectorBasis hM i₀
  -- heig : M.mulVec ((hM.eigenvectorBasis i₀).ofLp) = hM.eigenvalues i₀ • ...
  -- rayleighOnVec_eq_re_of_eigenvector expects ((eigval : ℝ) : ℂ) form
  have heig' : M.mulVec ((hM.eigenvectorBasis i₀).ofLp) =
      ((hM.eigenvalues i₀ : ℝ) : ℂ) • ((hM.eigenvectorBasis i₀).ofLp) := by
    convert heig using 2
  rw [rayleighOnVec_eq_re_of_eigenvector M _ _ heig'
        (eigenvectorBasis_dotProduct_self_eq_one hM i₀)]
  simp [hi₀]

end LatticeSystem.Quantum
