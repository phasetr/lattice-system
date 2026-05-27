import LatticeSystem.Quantum.SpinS.SingleIonLadderForm
import LatticeSystem.Quantum.SpinS.PlusMinusDiag

/-!
# Sign of the single-site `(Ŝ²)²` off-diagonal entries

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The off-diagonal (`i ≠ j`) entries of the single-site square `(Ŝ²)²` are **real and
non-positive**: in the ladder form `(Ŝ²)² = ¼(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺) − ¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)` the
`Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺` part is diagonal (vanishes off-diagonal) and the `Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻` part has real
non-negative entries, so the coefficient `−¼` makes the off-diagonal entry `≤ 0`.

With the crystal-field coefficient `D ≥ 0` (case (i)) and the same-site Marshall sign `+1` (the
`±2` shift is even), this gives the non-positive dressed single-ion off-diagonal contribution.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The square of a real-entry matrix has real entries. -/
theorem matrix_mul_self_apply_im_zero {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : ∀ i j, (A i j).im = 0) (i j : n) :
    ((A * A) i j).im = 0 := by
  rw [Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [Complex.mul_im, hA, hA, mul_zero, zero_mul, add_zero]

/-- The square of a real, entrywise-non-negative matrix has non-negative entries. -/
theorem matrix_mul_self_apply_re_nonneg {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : ∀ i j, (A i j).im = 0) (hAnn : ∀ i j, 0 ≤ (A i j).re) (i j : n) :
    0 ≤ ((A * A) i j).re := by
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_nonneg (fun k _ => ?_)
  rw [Complex.mul_re, hA, zero_mul, sub_zero]
  exact mul_nonneg (hAnn _ _) (hAnn _ _)

/-- Off-diagonal value of the single-site `(Ŝ²)²`: only the `−¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)` part survives. -/
theorem spinSOp2_mul_spinSOp2_apply_offdiag_eq (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    (spinSOp2 N * spinSOp2 N) i j =
      -(1 / 4 : ℂ) * ((spinSOpPlus N * spinSOpPlus N) i j +
        (spinSOpMinus N * spinSOpMinus N) i j) := by
  rw [spinSOp2_mul_spinSOp2_ladder_form, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul, Matrix.add_apply, Matrix.add_apply,
    spinSOpPlus_mul_spinSOpMinus_eq_diagonal, spinSOpMinus_mul_spinSOpPlus_eq_diagonal,
    Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  ring

/-- The single-site `(Ŝ²)²` off-diagonal entries are real (`im = 0`). -/
theorem spinSOp2_mul_spinSOp2_apply_offdiag_im_zero (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    ((spinSOp2 N * spinSOp2 N) i j).im = 0 := by
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hij, Complex.mul_im, Complex.add_im,
    matrix_mul_self_apply_im_zero (spinSOpPlus_apply_im_zero N),
    matrix_mul_self_apply_im_zero (spinSOpMinus_apply_im_zero N)]
  simp

/-- The single-site `(Ŝ²)²` off-diagonal entries have non-positive real part. -/
theorem spinSOp2_mul_spinSOp2_apply_offdiag_re_nonpos (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    ((spinSOp2 N * spinSOp2 N) i j).re ≤ 0 := by
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hij, Complex.mul_re]
  have hz : 0 ≤ ((spinSOpPlus N * spinSOpPlus N) i j +
      (spinSOpMinus N * spinSOpMinus N) i j).re := by
    rw [Complex.add_re]
    exact add_nonneg
      (matrix_mul_self_apply_re_nonneg (spinSOpPlus_apply_im_zero N)
        (spinSOpPlus_apply_re_nonneg N) i j)
      (matrix_mul_self_apply_re_nonneg (spinSOpMinus_apply_im_zero N)
        (spinSOpMinus_apply_re_nonneg N) i j)
  have hcre : (-(1 / 4 : ℂ)).re = -(1 / 4) := by simp
  have hcim : (-(1 / 4 : ℂ)).im = 0 := by simp
  rw [hcre, hcim, zero_mul, sub_zero]
  nlinarith [hz]

end LatticeSystem.Quantum
