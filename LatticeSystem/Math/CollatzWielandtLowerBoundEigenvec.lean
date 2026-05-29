import LatticeSystem.Math.CollatzWielandt

/-!
# Collatz-Wielandt lower bound at the abs of an eigenvector

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.e.2-4): For a nonneg matrix `A : Matrix n n ℝ` and a real eigenvector `w`
at eigenvalue `λ` (i.e., `A *ᵥ w = λ • w`) with `w ≠ 0`,
`|λ| ≤ collatzWielandtFn A (fun j => |w j|)`.

Built from three layered lemmas:
- (e.2) `abs_mulVec_le_mulVec_abs`: triangle inequality `|A *ᵥ w|_i ≤ (A *ᵥ |w|)_i`.
- (e.3) `abs_eigenvalue_mul_abs_le_mulVec_abs`: at an eigenvector, `|λ| * |w_i| ≤ (A *ᵥ |w|)_i`.
- (e.4) `abs_eigenvalue_le_collatzWielandtFn_abs`: CW inf ≥ |λ| over the support of |w|.

Used in (j.13.e) for `hermitianMaxEigenvalue B ≤ μ_PF` for nonneg symmetric
irreducible `B`.

Reference: E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.),
Springer 2006, §1.2.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix Finset

variable {n : Type*} [Fintype n]

/-- **(j.13.e.2) Triangle inequality for matrix-vector product** (nonneg matrix):
for nonneg `A` and real `w`, `|A *ᵥ w|_i ≤ (A *ᵥ |w|)_i`. -/
theorem abs_mulVec_le_mulVec_abs
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (w : n → ℝ) (i : n) :
    |A.mulVec w i| ≤ A.mulVec (fun j => |w j|) i := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, A i j * w j|
      ≤ ∑ j, |A i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, A i j * |w j| := by
        apply Finset.sum_congr rfl
        intros j _
        rw [abs_mul, abs_of_nonneg (hA i j)]

/-- **(j.13.e.3) At an eigenvector, `|λ| * |w_i| ≤ (A *ᵥ |w|)_i`** (nonneg matrix). -/
theorem abs_eigenvalue_mul_abs_le_mulVec_abs
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {lam : ℝ} {w : n → ℝ} (h_eig : A.mulVec w = lam • w) (i : n) :
    |lam| * |w i| ≤ A.mulVec (fun j => |w j|) i := by
  have h1 : |A.mulVec w i| = |lam| * |w i| := by
    rw [h_eig]; simp [abs_mul]
  rw [← h1]
  exact abs_mulVec_le_mulVec_abs hA w i

/-- **(j.13.e.4) CW lower bound at the abs of an eigenvector**.

For a nonneg matrix `A` and real eigenvector `w ≠ 0` at eigenvalue `λ`,
`|λ| ≤ collatzWielandtFn A (fun j => |w j|)`. -/
theorem abs_eigenvalue_le_collatzWielandtFn_abs
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {lam : ℝ} {w : n → ℝ} (hw_ne : w ≠ 0)
    (h_eig : A.mulVec w = lam • w) :
    |lam| ≤ collatzWielandtFn A (fun j => |w j|) := by
  -- Support of |w| is the set of indices with |w i| > 0, i.e., w i ≠ 0.
  -- Since w ≠ 0, this is nonempty.
  have h_supp_ne : ∃ j, 0 < |w j| := by
    by_contra h
    push Not at h
    apply hw_ne
    funext i
    have : |w i| = 0 := le_antisymm (h i) (abs_nonneg _)
    exact abs_eq_zero.mp this
  apply le_collatzWielandtFn_of_all_supp_ratios_le h_supp_ne
  intro i hwi_pos
  have h_bd : |lam| * |w i| ≤ A.mulVec (fun j => |w j|) i :=
    abs_eigenvalue_mul_abs_le_mulVec_abs hA h_eig i
  exact (le_div_iff₀ hwi_pos).mpr h_bd

end LatticeSystem.Math.CollatzWielandt
