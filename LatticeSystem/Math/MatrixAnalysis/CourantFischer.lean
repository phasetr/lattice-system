import LatticeSystem.Math.RayleighPosSemidefKernel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Towards the Courant–Fischer min–max principle and Weyl monotonicity (Issue #4338)

This file builds, from mathlib's Hermitian spectral theorem and the Loewner order, the ingredients
of Weyl eigenvalue monotonicity (Tasaki Theorem A.7), discharging
`hermitian_eigenvalues₀_monotone`.  See `.self-local/docs/courant-fischer-design.md`.

The first layer records the *pointwise Rayleigh monotonicity* of the (unnormalized) energy
quadratic form `rayleighOnVec M v = (star v ⬝ᵥ M v).re` under the Loewner order: `A ≤ B` is exactly
pointwise domination `rayleighOnVec A v ≤ rayleighOnVec B v`.  This is the comparison step that, fed
through the block/pigeonhole argument, yields Weyl monotonicity.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n]

/-- The (unnormalized) energy quadratic form is monotone in the Loewner order: if `A ≤ B` then
`rayleighOnVec A v ≤ rayleighOnVec B v` for every vector `v`.  This is the pointwise Rayleigh
monotonicity that powers the eigenvalue comparison of Tasaki Theorem A.7. -/
theorem rayleighOnVec_mono {A B : Matrix n n ℂ} (hAB : A ≤ B) (v : n → ℂ) :
    rayleighOnVec A v ≤ rayleighOnVec B v := by
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have h0 : (0 : ℝ) ≤ rayleighOnVec (B - A) v :=
    (Complex.le_def.mp (hps.dotProduct_mulVec_nonneg v)).1
  have hsplit : rayleighOnVec (B - A) v = rayleighOnVec B v - rayleighOnVec A v := by
    have hBA : B - A = B + ((-1 : ℝ) : ℂ) • A := by
      push_cast
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hBA, rayleighOnVec_add_matrix, rayleighOnVec_real_smul]
    ring
  linarith [hsplit ▸ h0]

open scoped InnerProductSpace in
open Module in
/-- **Spectral form of the Rayleigh quotient.**  For a symmetric operator `T` on
`EuclideanSpace ℂ n` with sorted eigenvalues `λ_i` and orthonormal eigenbasis `b`, the energy
`re ⟪x, T x⟫` is the eigenvalue-weighted sum `∑ᵢ λᵢ ‖⟨bᵢ, x⟩‖²`. -/
theorem isSymmetric_re_inner_self_eq_sum {T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    (hT : T.IsSymmetric) (hn : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
    (x : EuclideanSpace ℂ n) :
    RCLike.re (inner ℂ x (T x))
      = ∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ∀ (l : ℝ) (c : ℂ),
      RCLike.re ((starRingEnd ℂ) c * ((l : ℂ) * c)) = l * ‖c‖ ^ 2 := by
    intro l c
    have hnorm : ‖c‖ ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    rw [hnorm, RCLike.re_to_complex]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
    ring
  rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hn) x (T x), map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show inner ℂ x (hT.eigenvectorBasis hn i)
        = (starRingEnd ℂ) ((hT.eigenvectorBasis hn).repr x i) from by
      rw [(hT.eigenvectorBasis hn).repr_apply_apply, inner_conj_symm],
    show inner ℂ (hT.eigenvectorBasis hn i) (T x) = (hT.eigenvectorBasis hn).repr (T x) i from
      ((hT.eigenvectorBasis hn).repr_apply_apply (T x) i).symm,
    hT.eigenvectorBasis_apply_self_apply hn x i]
  exact key (hT.eigenvalues hn i) ((hT.eigenvectorBasis hn).repr x i)

open Module in
/-- **Parseval**: `‖x‖² = ∑ᵢ ‖⟨bᵢ, x⟩‖²` in an orthonormal eigenbasis. -/
theorem repr_norm_sq_sum {T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    (hT : T.IsSymmetric) (hn : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
    (x : EuclideanSpace ℂ n) :
    ‖x‖ ^ 2 = ∑ i, ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← LinearIsometryEquiv.norm_map (hT.eigenvectorBasis hn).repr x, EuclideanSpace.norm_sq_eq]

open scoped InnerProductSpace in
open Module in
/-- **Block lower bound.**  If the eigenbasis coordinates of `x` are supported where the
eigenvalue is `≥ c`, then `c‖x‖² ≤ re⟪x, T x⟫`. -/
theorem isSymmetric_block_lower {T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    (hT : T.IsSymmetric) (hn : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
    (x : EuclideanSpace ℂ n) (c : ℝ)
    (hc : ∀ i, (hT.eigenvectorBasis hn).repr x i ≠ 0 → c ≤ hT.eigenvalues hn i) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ x (T x)) := by
  rw [isSymmetric_re_inner_self_eq_sum hT hn x, repr_norm_sq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hz : (hT.eigenvectorBasis hn).repr x i = 0
  · simp [hz]
  · rw [mul_comm c, mul_comm (hT.eigenvalues hn i)]
    exact mul_le_mul_of_nonneg_left (hc i hz) (sq_nonneg _)

open scoped InnerProductSpace in
open Module in
/-- **Block upper bound.**  If the eigenbasis coordinates of `x` are supported where the
eigenvalue is `≤ c`, then `re⟪x, T x⟫ ≤ c‖x‖²`. -/
theorem isSymmetric_block_upper {T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    (hT : T.IsSymmetric) (hn : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
    (x : EuclideanSpace ℂ n) (c : ℝ)
    (hc : ∀ i, (hT.eigenvectorBasis hn).repr x i ≠ 0 → hT.eigenvalues hn i ≤ c) :
    RCLike.re (inner ℂ x (T x)) ≤ c * ‖x‖ ^ 2 := by
  rw [isSymmetric_re_inner_self_eq_sum hT hn x, repr_norm_sq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hz : (hT.eigenvectorBasis hn).repr x i = 0
  · simp [hz]
  · rw [mul_comm c, mul_comm (hT.eigenvalues hn i)]
    exact mul_le_mul_of_nonneg_left (hc i hz) (sq_nonneg _)

end LatticeSystem.Quantum
