import LatticeSystem.Math.CollatzWielandtUpperBoundSymmetric
import LatticeSystem.Math.CollatzWielandtLowerBoundEigenvec

/-!
# Real eigenvalue ≤ PF eigenvalue for symmetric nonneg matrices

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.e.5): For a symmetric nonneg matrix `A` with a strictly positive
eigenvector `v` at eigenvalue `μ`, for any real eigenvalue `λ` of `A` with
eigenvector `w ≠ 0`, `λ ≤ μ`.

**Proof.** From (j.13.e.4) applied to `w`:
  `|λ| ≤ collatzWielandtFn A (fun j => |w j|)`.
From (j.13.e.1) applied to `|w|` (nonneg, nonzero):
  `collatzWielandtFn A (fun j => |w j|) ≤ μ`.
Combining and using `λ ≤ |λ|`:
  `λ ≤ |λ| ≤ μ`.

This is the real-side combination step preceding the complex Hermitian bridge
(j.13.e.6).

Reference: E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.),
Springer 2006, §1.2.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix

variable {n : Type*} [Fintype n]

/-- **(j.13.e.5) Real eigenvalue ≤ PF eigenvalue** (symmetric nonneg case). -/
theorem real_eigenvalue_le_of_pos_eigenvector
    {A : Matrix n n ℝ} (hA_symm : A.IsSymm) (hA_nn : ∀ i j, 0 ≤ A i j)
    {μ : ℝ} {v : n → ℝ} (h_eig : A.mulVec v = μ • v) (hv_pos : ∀ i, 0 < v i)
    {lam : ℝ} {w : n → ℝ} (hw_ne : w ≠ 0) (hw_eig : A.mulVec w = lam • w) :
    lam ≤ μ := by
  -- |λ| ≤ CW(|w|).
  have h_low : |lam| ≤ collatzWielandtFn A (fun j => |w j|) :=
    abs_eigenvalue_le_collatzWielandtFn_abs hA_nn hw_ne hw_eig
  -- |w| nonneg, |w| ≠ 0.
  have hw_abs_nn : ∀ i, 0 ≤ (fun j => |w j|) i := fun i => abs_nonneg _
  have hw_abs_ne : (fun j => |w j|) ≠ 0 := by
    intro h
    apply hw_ne
    funext i
    have : |w i| = 0 := congrFun h i
    exact abs_eq_zero.mp this
  -- CW(|w|) ≤ μ.
  have h_up : collatzWielandtFn A (fun j => |w j|) ≤ μ :=
    collatzWielandtFn_le_of_pos_eigenvector hA_symm h_eig hv_pos hA_nn hw_abs_nn hw_abs_ne
  -- λ ≤ |λ| ≤ μ.
  exact (le_abs_self lam).trans (h_low.trans h_up)

end LatticeSystem.Math.CollatzWielandt
