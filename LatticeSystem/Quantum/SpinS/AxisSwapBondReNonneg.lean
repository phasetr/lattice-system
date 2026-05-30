import LatticeSystem.Quantum.SpinS.AxisSwapBondOffDiag

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Non-negativity of the axis-swapped bond off-diagonal entry (case (i))

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a bond `x ≠ y` and real anisotropy `λ` in the range `−1 ≤ λ ≤ 1` (case (i)), the off-diagonal
config entry of `spinSDotXXZSwap x y λ` has **non-negative real part**: the longitudinal
`Ŝ³Ŝ³` part is diagonal (vanishes off-diagonal), and the transverse / parity ladder entries are
real and non-negative (#3759) with coefficients `(1+λ)/4 ≥ 0`, `(1−λ)/4 ≥ 0`.

Together with `spinSDotXXZSwap_apply_im_zero` (#3762) this gives a real non-negative off-diagonal
bond entry, which the bipartite Marshall sign then flips to `≤ 0` (#3760).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- For case (i) (`−1 ≤ λ ≤ 1` real) the off-diagonal entry of the axis-swapped bond has
non-negative real part. -/
theorem spinSDotXXZSwap_apply_re_nonneg
    {x y : Λ} (hxy : x ≠ y) {lam : ℂ}
    (hlam : lam.im = 0) (hlam_lb : -1 ≤ lam.re) (hlam_ub : lam.re ≤ 1)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    0 ≤ (spinSDotXXZSwap x y lam N σ' σ).re := by
  have hladder := congrFun (congrFun (spinSDotXXZSwap_ladder_form (Λ := Λ) x y lam) σ') σ
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg hxy σ' σ
  have h3 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg hxy σ' σ
  have h4 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg hxy σ' σ
  -- coefficient real parts and vanishing imaginary parts.
  have hc1re : ((1 + lam) / 4).re = (1 + lam.re) / 4 := by
    simp [Complex.add_re]
  have hc1im : ((1 + lam) / 4).im = 0 := by simp [Complex.add_im, hlam]
  have hc2re : ((1 - lam) / 4).re = (1 - lam.re) / 4 := by
    simp [Complex.sub_re]
  have hc2im : ((1 - lam) / 4).im = 0 := by simp [Complex.sub_im, hlam]
  rw [hladder, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul,
    onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, add_zero,
    Complex.add_re, Complex.mul_re, Complex.mul_re, hc1re, hc1im, hc2re, hc2im,
    Matrix.add_apply, Matrix.add_apply, Complex.add_re, Complex.add_im, Complex.add_re,
    Complex.add_im, h1.1, h2.1, h3.1, h4.1]
  have ht : 0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) σ' σ).re +
      ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) σ' σ).re := add_nonneg h1.2 h2.2
  have hp : 0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N)) σ' σ).re +
      ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N)) σ' σ).re := add_nonneg h3.2 h4.2
  have hcoef1 : 0 ≤ (1 + lam.re) / 4 := by linarith
  have hcoef2 : 0 ≤ (1 - lam.re) / 4 := by linarith
  simp only [sub_zero, mul_zero, add_zero]
  exact add_nonneg (mul_nonneg hcoef1 ht) (mul_nonneg hcoef2 hp)
