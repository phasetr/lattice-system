import LatticeSystem.Quantum.SpinS.AxisSwapLadderForm
import LatticeSystem.Quantum.SpinS.AxisSwapLadderEntry

/-!
# Off-diagonal structure of the axis-swapped anisotropic bond

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a bond `x ≠ y`, the longitudinal part `Ŝ³_x Ŝ³_y` of the axis-swapped bond is **diagonal**
(its config-basis entries vanish off the diagonal), so every off-diagonal matrix element of
`spinSDotXXZSwap x y λ` comes from the transverse/parity ladder terms only.  Combined with the
realness of those ladder entries (#3759), the whole bond off-diagonal element is **real** for a
real anisotropy `λ` — the input needed to talk about its sign in the Marshall-dressed basis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The longitudinal bond `Ŝ³_x Ŝ³_y` (`x ≠ y`) has vanishing off-diagonal config entries:
it is a diagonal operator. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  split_ifs with hagree
  · -- agree off {x,y} but σ' ≠ σ ⟹ differ at x or y ⟹ a diagonal Ŝ³ factor vanishes.
    by_cases hx : σ' x = σ x
    · by_cases hy : σ' y = σ y
      · exact absurd (funext fun k => by
          by_cases hkx : k = x
          · rw [hkx]; exact hx
          · by_cases hky : k = y
            · rw [hky]; exact hy
            · exact hagree k hkx hky) hne
      · rw [spinSOp3_apply_offdiag N hy, mul_zero]
    · rw [spinSOp3_apply_offdiag N hx, zero_mul]
  · rfl

/-- The axis-swapped bond off-diagonal entry is **real** for a real anisotropy `λ`: the `Ŝ³Ŝ³`
part is diagonal and the transverse/parity ladder entries are real. -/
theorem spinSDotXXZSwap_apply_im_zero
    {x y : Λ} (hxy : x ≠ y) {lam : ℂ} (hlam : lam.im = 0)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (spinSDotXXZSwap x y lam N σ' σ).im = 0 := by
  have hladder := congrFun (congrFun (spinSDotXXZSwap_ladder_form (Λ := Λ) x y lam) σ') σ
  have h1 := (onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg hxy σ' σ).1
  have h2 := (onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg hxy σ' σ).1
  have h3 := (onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg hxy σ' σ).1
  have h4 := (onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg hxy σ' σ).1
  have hc1 : ((1 + lam) / 4).im = 0 := by simp [Complex.add_im, hlam]
  have hc2 : ((1 - lam) / 4).im = 0 := by simp [Complex.sub_im, hlam]
  rw [hladder, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul,
    onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, add_zero,
    Complex.add_im, Complex.mul_im, Complex.mul_im, hc1, hc2,
    Matrix.add_apply, Matrix.add_apply, Complex.add_im, Complex.add_im, h1, h2, h3, h4]
  ring
