import LatticeSystem.Math.CollatzWielandt
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Collatz-Wielandt upper bound for symmetric irreducible matrices

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.e.1): For a symmetric nonneg matrix `A` with a strictly positive eigenvector
`v > 0` at eigenvalue `μ` (i.e., `A v = μ v`), for any nonneg `x ≠ 0`, we have
`collatzWielandtFn A x ≤ μ`.

Proof: from `r := collatzWielandtFn A x`, `le_mulVec` gives `r • x ≤ A *ᵥ x`
pointwise. Dotting with `v`:
```
r * (∑ v_i x_i) = ∑ v_i (r * x_i) ≤ ∑ v_i (A *ᵥ x)_i = (by symmetry) ∑ (A v)_i x_i = μ * (∑ v_i x_i)
```
Since `∑ v_i x_i > 0` (v > 0, x ≥ 0, x ≠ 0), divide to get `r ≤ μ`.

This is the upper bound side of the Collatz-Wielandt characterization, used in
(j.13.e) to derive `hermitianMaxEigenvalue B ≤ μ_PF` for nonneg irreducible
symmetric `B`.

Reference: E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.),
Springer 2006, §1.2.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix Finset

variable {n : Type*} [Fintype n]

/-- **Collatz-Wielandt upper bound at a positive eigenvalue** (symmetric case).

For a symmetric matrix `A : Matrix n n ℝ` with a strictly positive eigenvector `v`
at eigenvalue `μ` (i.e., `A *ᵥ v = μ • v`, `v > 0`), for any nonneg `x ≠ 0`,
`collatzWielandtFn A x ≤ μ`.

Used by (j.13.e) for `hermitianMaxEigenvalue B ≤ μ_PF`. -/
theorem collatzWielandtFn_le_of_pos_eigenvector
    {A : Matrix n n ℝ} (hA_symm : A.IsSymm)
    {μ : ℝ} {v : n → ℝ} (h_eig : A *ᵥ v = μ • v) (hv_pos : ∀ i, 0 < v i)
    (hA_nn : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx_nn : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
    collatzWielandtFn A x ≤ μ := by
  set r := collatzWielandtFn A x with hr_def
  -- Step 1: r • x ≤ A *ᵥ x pointwise (fundamental inequality).
  have h_rx_le : r • x ≤ A *ᵥ x := le_mulVec hA_nn hx_nn
  -- Step 2: dot product with v preserves the inequality (v ≥ 0).
  have h_dot_le : ∑ i, v i * (r • x) i ≤ ∑ i, v i * (A *ᵥ x) i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (h_rx_le i) (le_of_lt (hv_pos i))
  -- Step 3: LHS = r * ∑ v_i x_i.
  have h_lhs : ∑ i, v i * (r • x) i = r * ∑ i, v i * x i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros; ring
  -- Step 4: RHS = ∑_i v_i (∑_j A_ij x_j)
  --             = (by symmetry A_ij = A_ji) ∑_j x_j (A v)_j
  --             = μ * ∑ v_i x_i.
  have h_rhs : ∑ i, v i * (A *ᵥ x) i = μ * ∑ i, v i * x i := by
    -- ∑_i v_i ∑_j A_ij x_j = ∑_i ∑_j v_i A_ij x_j = ∑_j ∑_i v_i A_ij x_j
    -- = ∑_j x_j ∑_i A_ij v_i = (by symmetry A_ij = A_ji) ∑_j x_j ∑_i A_ji v_i
    -- = ∑_j x_j (A v)_j = ∑_j x_j (μ v_j) = μ ∑ v_j x_j.
    have h_eq : ∑ i, v i * (A *ᵥ x) i = ∑ j, x j * (A *ᵥ v) j := by
      have h_expand_l : ∀ i, v i * (A *ᵥ x) i = ∑ j, v i * A i j * x j := by
        intro i
        simp only [mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros j _; ring
      have h_expand_r : ∀ j, x j * (A *ᵥ v) j = ∑ i, x j * A j i * v i := by
        intro j
        simp only [mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros i _; ring
      calc ∑ i, v i * (A *ᵥ x) i
          = ∑ i, ∑ j, v i * A i j * x j := by
            apply Finset.sum_congr rfl
            intros i _; exact h_expand_l i
        _ = ∑ j, ∑ i, v i * A i j * x j := Finset.sum_comm
        _ = ∑ j, ∑ i, x j * A j i * v i := by
            apply Finset.sum_congr rfl
            intros j _
            apply Finset.sum_congr rfl
            intros i _
            have hsym : A i j = A j i := Matrix.IsSymm.apply hA_symm j i
            rw [hsym]; ring
        _ = ∑ j, x j * (A *ᵥ v) j := by
            apply Finset.sum_congr rfl
            intros j _; exact (h_expand_r j).symm
    rw [h_eq, h_eig]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros j _; ring
  -- Step 5: ∑ v_i x_i > 0.
  have h_sum_pos : 0 < ∑ i, v i * x i := by
    have hex : ∃ j, 0 < x j := by
      by_contra h
      push Not at h
      exact hx_ne (funext fun i => le_antisymm (h i) (hx_nn i))
    obtain ⟨j, hj⟩ := hex
    apply Finset.sum_pos'
    · intros i _; exact mul_nonneg (le_of_lt (hv_pos i)) (hx_nn i)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hv_pos j) hj⟩
  -- Step 6: combine h_dot_le, h_lhs, h_rhs to get r * S ≤ μ * S, then divide.
  have h_combined : r * (∑ i, v i * x i) ≤ μ * (∑ i, v i * x i) := by
    rw [← h_lhs, ← h_rhs]; exact h_dot_le
  exact le_of_mul_le_mul_right h_combined h_sum_pos

end LatticeSystem.Math.CollatzWielandt
