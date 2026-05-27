import LatticeSystem.Quantum.SpinS.SpinSTransverseLadder
import LatticeSystem.Quantum.SpinS.MultiSite

/-!
# Two-site transverse bond in ladder form

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The two-site transverse bond `Ŝ¹_x Ŝ¹_y + Ŝ²_x Ŝ²_y` equals `½(Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)`,
the bond-level (cross-site) version of the single-site identity #3742.  This is the form
Tasaki uses to rewrite the XXZ transverse coupling (2.5.16) into ladder operators for the
Marshall-sign analysis of Theorem 2.4.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.16).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Two-site transverse bond in ladder form**:
`Ŝ¹_x Ŝ¹_y + Ŝ²_x Ŝ²_y = ½(Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)`. -/
theorem onSiteS_spinSOp1_mul_add_onSiteS_spinSOp2_mul (x y : Λ) :
    onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
        onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) =
      (1 / 2 : ℂ) • (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
        onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) := by
  have hI : (1 / (2 * I) : ℂ) * (1 / (2 * I)) = -(1 / 4) := by
    rw [div_mul_div_comm, one_mul, show (2 * I) * (2 * I) = 4 * (I * I) by ring, Complex.I_mul_I]
    norm_num
  rw [spinSOp1, spinSOp2]
  simp only [onSiteS_smul, onSiteS_add, onSiteS_sub]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hI, show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num,
    mul_add, add_mul, add_mul, mul_sub, sub_mul, sub_mul]
  module

/-- **Two-site difference of squares in ladder form**:
`Ŝ¹_x Ŝ¹_y − Ŝ²_x Ŝ²_y = ½(Ŝ⁺_x Ŝ⁺_y + Ŝ⁻_x Ŝ⁻_y)`. -/
theorem onSiteS_spinSOp1_mul_sub_onSiteS_spinSOp2_mul (x y : Λ) :
    onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) -
        onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) =
      (1 / 2 : ℂ) • (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) +
        onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N)) := by
  have hI : (1 / (2 * I) : ℂ) * (1 / (2 * I)) = -(1 / 4) := by
    rw [div_mul_div_comm, one_mul, show (2 * I) * (2 * I) = 4 * (I * I) by ring, Complex.I_mul_I]
    norm_num
  rw [spinSOp1, spinSOp2]
  simp only [onSiteS_smul, onSiteS_add, onSiteS_sub]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hI, show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num,
    mul_add, add_mul, add_mul, mul_sub, sub_mul, sub_mul]
  module

end LatticeSystem.Quantum
