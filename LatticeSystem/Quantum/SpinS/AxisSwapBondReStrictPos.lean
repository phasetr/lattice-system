import LatticeSystem.Quantum.SpinS.AxisSwapBondReNonneg
import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Strict positivity of the axis-swapped bond off-diagonal entry on a transverse step (case (i)
strict)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

On a `RaiseLowerStepS` witness — `σ' = σ` off `{x, y}` with `σ_x, σ_y` shifted in *opposite* Fin
directions by ±1 — and under case (i) strict (`−1 < λ ≤ 1` real), the off-diagonal entry of
`spinSDotXXZSwap x y λ` has **strictly positive** real part:

* Exactly one of the four transverse / parity ladder products is non-vanishing, namely
  the *matching* transverse term (`Ŝ⁻_x Ŝ⁺_y` in case 1, `Ŝ⁺_x Ŝ⁻_y` in case 2 of the
  `RaiseLowerStepS` direction).
* The matching transverse term has strict positive real factor at both sites
  (`spinSOpPlus_apply_re_pos_of_raise`, `spinSOpMinus_apply_re_pos_of_lower`).
* The two parity ladder terms (`Ŝ⁺Ŝ⁺`, `Ŝ⁻Ŝ⁻`) and the off-direction transverse term vanish by
  Fin-index mismatch.
* `Ŝ³Ŝ³` vanishes off the diagonal.

Combined with the coefficient `(1 + λ)/4 > 0` (strict from `λ.re > −1`) this gives the strict
positive bond real part — the input to (c) step-positivity for the transverse `RaiseLowerStepS`
move in PR5 (parity-block Perron–Frobenius irreducibility).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Generic on-site mul-apply for a Plus-Plus product at the off-two-site agreement region. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ =
      spinSOpPlus N (σ' x) (σ x) * spinSOpPlus N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- Generic on-site mul-apply for a Minus-Minus product at the off-two-site agreement region. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ =
      spinSOpMinus N (σ' x) (σ x) * spinSOpMinus N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-! ## Case 1: `(σ x).val + 1 = (σ' x).val` and `(σ' y).val + 1 = (σ y).val`.
At `x`: matches `spinSOpMinus`.  At `y`: matches `spinSOpPlus`.  The matching transverse term is
`Ŝ⁻_x Ŝ⁺_y`; the other transverse term and both parity terms vanish. -/

/-- Case 1: `Ŝ⁻_x Ŝ⁺_y` strict positive real part. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_re_pos_case1
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 1 = (σ' x).val) (hsy : (σ' y).val + 1 = (σ y).val)
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
    Complex.mul_re, spinSOpMinus_apply_im_zero, spinSOpPlus_apply_im_zero, mul_zero, sub_zero]
  exact mul_pos (spinSOpMinus_apply_re_pos_of_lower N hsx)
    (spinSOpPlus_apply_re_pos_of_raise N hsy)

/-- Case 1: `Ŝ⁺_x Ŝ⁻_y` vanishes (off-direction transverse). -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_case1
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 1 = (σ' x).val) (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
    spinSOpPlus_apply_other N (by omega : (σ' x).val + 1 ≠ (σ x).val), zero_mul]

/-- Case 1: `Ŝ⁺_x Ŝ⁺_y` vanishes (parity mismatch at `x`). -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_eq_zero_case1
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 1 = (σ' x).val) (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
    spinSOpPlus_apply_other N (by omega : (σ' x).val + 1 ≠ (σ x).val), zero_mul]

/-- Case 1: `Ŝ⁻_x Ŝ⁻_y` vanishes (parity mismatch at `y`). -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_eq_zero_case1
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsy : (σ' y).val + 1 = (σ y).val) (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
    spinSOpMinus_apply_other N (by omega : (σ y).val + 1 ≠ (σ' y).val), mul_zero]

/-! ## Case 2: `(σ' x).val + 1 = (σ x).val` and `(σ y).val + 1 = (σ' y).val`.
At `x`: matches `spinSOpPlus`.  At `y`: matches `spinSOpMinus`. -/

/-- Case 2: `Ŝ⁺_x Ŝ⁻_y` strict positive real part. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_re_pos_case2
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ' x).val + 1 = (σ x).val) (hsy : (σ y).val + 1 = (σ' y).val)
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
    Complex.mul_re, spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero, mul_zero, sub_zero]
  exact mul_pos (spinSOpPlus_apply_re_pos_of_raise N hsx)
    (spinSOpMinus_apply_re_pos_of_lower N hsy)

/-- Case 2: `Ŝ⁻_x Ŝ⁺_y` vanishes. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_case2
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ' x).val + 1 = (σ x).val) (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
    spinSOpMinus_apply_other N (by omega : (σ x).val + 1 ≠ (σ' x).val), zero_mul]

/-- Case 2: `Ŝ⁺_x Ŝ⁺_y` vanishes (parity mismatch at `y`). -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_eq_zero_case2
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsy : (σ y).val + 1 = (σ' y).val) (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
    spinSOpPlus_apply_other N (by omega : (σ' y).val + 1 ≠ (σ y).val), mul_zero]

/-- Case 2: `Ŝ⁻_x Ŝ⁻_y` vanishes (parity mismatch at `x`). -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_eq_zero_case2
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ' x).val + 1 = (σ x).val) (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
    spinSOpMinus_apply_other N (by omega : (σ x).val + 1 ≠ (σ' x).val), zero_mul]

/-- **Strict positivity of the axis-swapped bond entry on a transverse witness, case (i) strict.**
For `−1 < λ.re ≤ 1` (real `λ`) and a `RaiseLowerStepS` witness on `{x, y}`,
`Re(spinSDotXXZSwap x y λ N σ' σ) > 0`. -/
theorem spinSDotXXZSwap_apply_re_pos_of_raiseLowerStepS_witness
    {x y : Λ} (hxy : x ≠ y) {lam : ℂ}
    (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < (spinSDotXXZSwap x y lam N σ' σ).re := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [he] at hsx; omega
  have hladder := congrFun (congrFun (spinSDotXXZSwap_ladder_form (Λ := Λ) x y lam) σ') σ
  have hc1re : ((1 + lam) / 4).re = (1 + lam.re) / 4 := by simp [Complex.add_re]
  have hc1im : ((1 + lam) / 4).im = 0 := by simp [Complex.add_im, hlam]
  have hc2re : ((1 - lam) / 4).re = (1 - lam.re) / 4 := by simp [Complex.sub_re]
  have hc2im : ((1 - lam) / 4).im = 0 := by simp [Complex.sub_im, hlam]
  rw [hladder, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul,
    onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, add_zero,
    Complex.add_re, Complex.mul_re, Complex.mul_re, hc1re, hc1im, hc2re, hc2im,
    Matrix.add_apply, Matrix.add_apply, Complex.add_re, Complex.add_im, Complex.add_re,
    Complex.add_im]
  simp only [sub_zero, zero_mul]
  have hcoef1 : 0 < (1 + lam.re) / 4 := by linarith
  rcases hsh with ⟨hsx, hsy⟩ | ⟨hsx, hsy⟩
  · -- Case 1: matching = Minus_x * Plus_y, strict positive; others = 0.
    have h1 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_case1 hxy hsx hagree,
        Complex.zero_re]
    have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_re_pos_case1 hxy hsx hsy hagree
    have h3 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_eq_zero_case1 hxy hsx hagree,
        Complex.zero_re]
    have h4 : ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_eq_zero_case1 hxy hsy hagree,
        Complex.zero_re]
    rw [h1, h3, h4, zero_add, add_zero, mul_zero, add_zero]
    exact mul_pos hcoef1 h2
  · -- Case 2: matching = Plus_x * Minus_y, strict positive; others = 0.
    have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_re_pos_case2 hxy hsx hsy hagree
    have h2 : ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_case2 hxy hsx hagree,
        Complex.zero_re]
    have h3 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_eq_zero_case2 hxy hsy hagree,
        Complex.zero_re]
    have h4 : ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_eq_zero_case2 hxy hsx hagree,
        Complex.zero_re]
    rw [h2, h3, h4, add_zero, add_zero, mul_zero, add_zero]
    exact mul_pos hcoef1 h1

end LatticeSystem.Quantum
