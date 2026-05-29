import LatticeSystem.Math.RealEigenvalueLePF
import LatticeSystem.Math.HermitianMaxEigenvalue
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Complex Hermitian max eigenvalue ≤ PF eigenvalue for real symmetric nonneg matrices

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.e.6): For a real symmetric nonneg matrix `B_real : Matrix n n ℝ` with a
strictly positive eigenvector `v` at eigenvalue `μ`, the complex Hermitian view
`B_complex := B_real.map (algebraMap ℝ ℂ)` satisfies
`hermitianMaxEigenvalue (B_complex).IsHermitian ≤ μ`.

**Proof.** From any complex eigenvector `w_complex` of `B_complex` at a real
eigenvalue `λ`, set `wAbs i := ‖w_complex i‖` (complex modulus, a real vector).
Then:
- `(B_real *ᵥ wAbs)_i ≥ ‖(B_complex *ᵥ w_complex)_i‖ = |λ| * wAbs i` (triangle
  inequality with `B_real ≥ 0`).
- `wAbs ≠ 0` since `w_complex ≠ 0`.
- By the CW lower bound: `|λ| ≤ collatzWielandtFn B_real wAbs`.
- By (j.13.e.1) at `wAbs`: `collatzWielandtFn B_real wAbs ≤ μ`.
- Combining: `λ ≤ |λ| ≤ μ`.

Applied at the eigenvalue `hermitianMaxEigenvalue B_complex` (obtained via
`hermitian_max_eigenvalue_mem_image` + `mulVec_eigenvectorBasis`), this gives
`hermitianMaxEigenvalue B_complex ≤ μ`.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Fintype n] [DecidableEq n] [Nonempty n] in
/-- **Real symmetric matrix lifted to ℂ is Hermitian**. -/
theorem isHermitian_map_ofReal_of_isSymm
    {B_real : Matrix n n ℝ} (hsymm : B_real.IsSymm) :
    (B_real.map (algebraMap ℝ ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  -- (B_complex)ᴴ i j = conj (B_complex j i) = conj (ofReal B_real j i)
  --                  = ofReal B_real j i = ofReal B_real i j = B_complex i j.
  have hsym : B_real j i = B_real i j := Matrix.IsSymm.apply hsymm i j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply, hsym]

omit [DecidableEq n] [Nonempty n] in
/-- **Triangle inequality for `B_real ≥ 0` and complex `w`**: at each `i`,
`‖(B_complex *ᵥ w) i‖ ≤ (B_real *ᵥ (fun j => ‖w j‖)) i`. -/
theorem norm_mulVec_complex_le_mulVec_norm
    {B_real : Matrix n n ℝ} (hnn : ∀ i j, 0 ≤ B_real i j) (w : n → ℂ) (i : n) :
    ‖((B_real.map (algebraMap ℝ ℂ)) *ᵥ w) i‖ ≤
      B_real.mulVec (fun j => ‖w j‖) i := by
  -- LHS = ‖∑ j, (B_real i j : ℂ) * w j‖
  -- ≤ ∑ j, ‖(B_real i j : ℂ) * w j‖ = ∑ j, |B_real i j| * ‖w j‖ = ∑ j, B_real i j * ‖w j‖.
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  show ‖∑ j, ((B_real i j : ℂ)) * w j‖ ≤ ∑ j, B_real i j * ‖w j‖
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intros j _
  rw [norm_mul]
  have hnorm : ‖((B_real i j : ℂ))‖ = B_real i j := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hnn i j)]
  rw [hnorm]

/-- **(j.13.e.6) Complex Hermitian max eigenvalue ≤ PF eigenvalue**.

For a real symmetric nonneg matrix `B_real` with strictly positive eigenvector
`v` at `μ`, `hermitianMaxEigenvalue (B_real.map ofReal).IsHermitian ≤ μ`. -/
theorem hermitianMaxEigenvalue_le_of_pos_eigenvector
    {B_real : Matrix n n ℝ} (hsymm : B_real.IsSymm) (hnn : ∀ i j, 0 ≤ B_real i j)
    {μ : ℝ} {v : n → ℝ} (h_eig : B_real.mulVec v = μ • v) (hv_pos : ∀ i, 0 < v i) :
    LatticeSystem.Math.hermitianMaxEigenvalue (isHermitian_map_ofReal_of_isSymm hsymm) ≤ μ := by
  set hHerm := isHermitian_map_ofReal_of_isSymm (B_real := B_real) hsymm
  -- max ∈ image of eigenvalues.
  have h_in : LatticeSystem.Math.hermitianMaxEigenvalue hHerm ∈
      (Finset.univ : Finset n).image hHerm.eigenvalues :=
    LatticeSystem.Math.hermitian_max_eigenvalue_mem_image hHerm
  rw [Finset.mem_image] at h_in
  obtain ⟨i, _, hi_eq⟩ := h_in
  -- Use eigenvectorBasis at i.
  set w_complex : n → ℂ := ⇑(hHerm.eigenvectorBasis i) with hw_def
  set lam : ℝ := hHerm.eigenvalues i with hlam_def
  have h_eig_c : (B_real.map (algebraMap ℝ ℂ)) *ᵥ w_complex =
      ((lam : ℂ)) • w_complex := hHerm.mulVec_eigenvectorBasis i
  have hw_ne : w_complex ≠ 0 := by
    intro h
    have hne := hHerm.eigenvectorBasis.orthonormal.ne_zero i
    exact hne ((@WithLp.ofLp_eq_zero 2 (n → ℂ) _ _).mp h)
  -- Set wAbs := ‖w_complex ·‖.
  set wAbs : n → ℝ := fun j => ‖w_complex j‖ with hwAbs_def
  -- wAbs is nonneg, nonzero.
  have hwAbs_nn : ∀ k, 0 ≤ wAbs k := fun k => norm_nonneg _
  have hwAbs_ne : wAbs ≠ 0 := by
    intro h
    apply hw_ne
    funext k
    have : ‖w_complex k‖ = 0 := congrFun h k
    exact norm_eq_zero.mp this
  -- (B_real *ᵥ wAbs) k ≥ |lam| * wAbs k for all k.
  have h_bd : ∀ k, |lam| * wAbs k ≤ B_real.mulVec wAbs k := fun k => by
    have h1 := norm_mulVec_complex_le_mulVec_norm hnn w_complex k
    -- h1: ‖(B_complex *ᵥ w_complex) k‖ ≤ (B_real *ᵥ wAbs) k.
    -- (B_complex *ᵥ w_complex) k = (lam : ℂ) * w_complex k.
    -- ‖(lam : ℂ) * w_complex k‖ = |lam| * ‖w_complex k‖ = |lam| * wAbs k.
    have h2 : ‖((B_real.map (algebraMap ℝ ℂ)) *ᵥ w_complex) k‖ = |lam| * wAbs k := by
      rw [h_eig_c]
      show ‖((lam : ℂ) • w_complex) k‖ = |lam| * wAbs k
      rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    linarith [h1, h2.symm.le]
  -- CW(wAbs) ≥ |lam|.
  have h_cw_low : |lam| ≤ collatzWielandtFn B_real wAbs := by
    obtain ⟨k0, hk0⟩ : ∃ k, 0 < wAbs k := by
      by_contra h
      push Not at h
      apply hwAbs_ne
      funext k
      exact le_antisymm (h k) (hwAbs_nn k)
    apply le_collatzWielandtFn_of_all_supp_ratios_le ⟨k0, hk0⟩
    intros k hk_pos
    -- (B_real *ᵥ wAbs) k / wAbs k ≥ |lam|.
    have := h_bd k
    exact (le_div_iff₀ hk_pos).mpr this
  -- CW(wAbs) ≤ μ.
  have h_cw_up : collatzWielandtFn B_real wAbs ≤ μ :=
    collatzWielandtFn_le_of_pos_eigenvector hsymm h_eig hv_pos hnn hwAbs_nn hwAbs_ne
  -- lam ≤ |lam| ≤ CW(wAbs) ≤ μ.
  have hlam_le : lam ≤ μ := (le_abs_self lam).trans (h_cw_low.trans h_cw_up)
  -- Conclude.
  rw [← hi_eq]; exact hlam_le

end LatticeSystem.Math.CollatzWielandt
