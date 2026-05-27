import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.TwoSiteTransverseLadder

/-!
# Ladder form of the axis-swapped anisotropic bond (Tasaki (2.5.16))

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The axis-swapped two-site bond `Ŝ¹_x Ŝ¹_y + λ Ŝ²_x Ŝ²_y + Ŝ³_x Ŝ³_y` (anisotropy now in the
transverse plane) rewrites in raising/lowering form as
`(1+λ)/4 (Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y) + (1−λ)/4 (Ŝ⁺_x Ŝ⁺_y + Ŝ⁻_x Ŝ⁻_y) + Ŝ³_x Ŝ³_y`.

This is Tasaki's eq. (2.5.16).  The decisive feature for Theorem 2.4 is the
`(1−λ)/4 (Ŝ⁺_x Ŝ⁺_y + Ŝ⁻_x Ŝ⁻_y)` term: it changes the total magnetization by `±2`, coupling the
`Ŝ³_tot` sectors into the two **parity** blocks (even/odd), where the Marshall-sign
Perron–Frobenius argument yields at-most-double degeneracy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.16).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Ladder form of the axis-swapped bond** (Tasaki (2.5.16)):
`Ŝ¹_x Ŝ¹_y + λ Ŝ²_x Ŝ²_y + Ŝ³_x Ŝ³_y =
  (1+λ)/4 (Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y) + (1−λ)/4 (Ŝ⁺_x Ŝ⁺_y + Ŝ⁻_x Ŝ⁻_y) + Ŝ³_x Ŝ³_y`. -/
theorem spinSDotXXZSwap_ladder_form (x y : Λ) (lam : ℂ) :
    spinSDotXXZSwap x y lam N =
      ((1 + lam) / 4) • (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) +
        ((1 - lam) / 4) • (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N)) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := by
  have hI : (1 / (2 * I) : ℂ) * (1 / (2 * I)) = -(1 / 4) := by
    rw [div_mul_div_comm, one_mul, show (2 * I) * (2 * I) = 4 * (I * I) by ring, Complex.I_mul_I]
    norm_num
  rw [spinSDotXXZSwap_def, spinSOp1, spinSOp2]
  simp only [onSiteS_smul, onSiteS_add, onSiteS_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub]
  rw [hI]
  module

end LatticeSystem.Quantum
