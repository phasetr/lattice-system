import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDef

/-!
# The sublattice Casimir is positive semidefinite

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
toy minimum-energy bound ingredient (see
`.self-local/tex/3716-tasaki-2-5-toy-min-energy-bound.tex`).

`(Ŝ_A)² = Ŝ_A^(1)² + Ŝ_A^(2)² + Ŝ_A^(3)²` is a sum of squares of Hermitian operators,
hence positive semidefinite: every eigenvalue has non-negative real part.  This lets us
write the Casimir eigenvalue as `a(a+1)` with a *real* sublattice spin `a ≥ 0`, the
form the coupled total-spin lower bound consumes.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The conjugated quadratic form `⟨v, Mᴴ M v⟩` is a non-negative real. -/
private theorem star_dotProduct_conjTranspose_mul_re_nonneg
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    0 ≤ (star v ⬝ᵥ (M.conjTranspose * M).mulVec v).re := by
  have heq : star v ⬝ᵥ (M.conjTranspose * M).mulVec v =
      ((∑ i, Complex.normSq ((M.mulVec v) i) : ℝ) : ℂ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  rw [heq, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

/-- **The sublattice Casimir is positive semidefinite**: any `(Ŝ_A)²`-eigenvalue `γ`
(for a non-zero eigenvector) has `0 ≤ γ.re`. -/
theorem sublatticeSpinSquaredS_eigenvalue_re_nonneg (A : Λ → Bool)
    {γ : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv_ne : v ≠ 0)
    (hcas : (sublatticeSpinSquaredS N A).mulVec v = γ • v) :
    0 ≤ γ.re := by
  -- ⟨v, (Ŝ_A)² v⟩ = γ ⟨v, v⟩ and = Σ_α ‖Ŝ_A^(α) v‖² ≥ 0.
  have hquad : star v ⬝ᵥ (sublatticeSpinSquaredS N A).mulVec v = γ * (star v ⬝ᵥ v) := by
    rw [hcas, dotProduct_smul, smul_eq_mul]
  have hsum : star v ⬝ᵥ (sublatticeSpinSquaredS N A).mulVec v =
      star v ⬝ᵥ ((sublatticeSpinSOp1 N A).conjTranspose * sublatticeSpinSOp1 N A).mulVec v +
      star v ⬝ᵥ ((sublatticeSpinSOp2 N A).conjTranspose * sublatticeSpinSOp2 N A).mulVec v +
      star v ⬝ᵥ ((sublatticeSpinSOp3 N A).conjTranspose * sublatticeSpinSOp3 N A).mulVec v := by
    rw [sublatticeSpinSquaredS_def, sublatticeSpinSOp1_sq_eq_conjTranspose_mul,
      sublatticeSpinSOp2_sq_eq_conjTranspose_mul, sublatticeSpinSOp3_sq_eq_conjTranspose_mul,
      Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add]
  have hnn : 0 ≤ (star v ⬝ᵥ (sublatticeSpinSquaredS N A).mulVec v).re := by
    rw [hsum, Complex.add_re, Complex.add_re]
    have h1 := star_dotProduct_conjTranspose_mul_re_nonneg (sublatticeSpinSOp1 N A) v
    have h2 := star_dotProduct_conjTranspose_mul_re_nonneg (sublatticeSpinSOp2 N A) v
    have h3 := star_dotProduct_conjTranspose_mul_re_nonneg (sublatticeSpinSOp3 N A) v
    linarith
  -- (star v ⬝ᵥ v) is a positive real; conclude γ.re ≥ 0.
  have hself : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    rw [dotProduct, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  have hself_pos : 0 < (∑ i, Complex.normSq (v i) : ℝ) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv_ne
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (Complex.normSq_nonneg _)
        (Ne.symm (by simpa [Complex.normSq_eq_zero] using hi))⟩
  rw [hquad, hself, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hnn
  nlinarith [hnn, hself_pos]

end LatticeSystem.Quantum
