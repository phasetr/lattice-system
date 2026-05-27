import LatticeSystem.Quantum.SpinS.Operators

/-!
# Transverse spin operators in terms of the ladder operators

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The transverse combination `Ŝ¹Ŝ¹ + Ŝ²Ŝ²` equals `½(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺)`, and the difference of
squares `Ŝ¹Ŝ¹ − Ŝ²Ŝ²` equals `½(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)`.  These are the single-site identities behind
Tasaki's rewriting (2.5.16) of the anisotropic XXZ Hamiltonian into ladder form, which the
Marshall-sign analysis for Theorem 2.4 uses.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.16).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `(1/(2i))² = −1/4`. -/
private theorem inv_two_I_sq : (1 / (2 * I) : ℂ) * (1 / (2 * I)) = -(1 / 4) := by
  rw [div_mul_div_comm, one_mul,
    show (2 * I) * (2 * I) = 4 * (I * I) by ring, Complex.I_mul_I]
  norm_num

/-- **Transverse-to-ladder identity** (longitudinal-preserving):
`Ŝ¹Ŝ¹ + Ŝ²Ŝ² = ½(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺)`. -/
theorem spinSOp1_mul_spinSOp1_add_spinSOp2_mul_spinSOp2 (N : ℕ) :
    spinSOp1 N * spinSOp1 N + spinSOp2 N * spinSOp2 N =
      (1 / 2 : ℂ) • (spinSOpPlus N * spinSOpMinus N + spinSOpMinus N * spinSOpPlus N) := by
  rw [spinSOp1, spinSOp2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_two_I_sq, show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num,
    mul_add, add_mul, add_mul, mul_sub, sub_mul, sub_mul]
  module

/-- **Difference-of-squares to ladder identity** (longitudinal-flipping):
`Ŝ¹Ŝ¹ − Ŝ²Ŝ² = ½(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)`. -/
theorem spinSOp1_mul_spinSOp1_sub_spinSOp2_mul_spinSOp2 (N : ℕ) :
    spinSOp1 N * spinSOp1 N - spinSOp2 N * spinSOp2 N =
      (1 / 2 : ℂ) • (spinSOpPlus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N) := by
  rw [spinSOp1, spinSOp2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_two_I_sq, show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num,
    mul_add, add_mul, add_mul, mul_sub, sub_mul, sub_mul]
  module

end LatticeSystem.Quantum
