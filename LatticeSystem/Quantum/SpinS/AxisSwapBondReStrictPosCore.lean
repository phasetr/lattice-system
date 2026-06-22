import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement

/-!
# Axis-swap bond strict positivity: per-case lemmas (foundation)

Foundational layer extracted from `AxisSwapBondReStrictPos.lean` for build speed.  This file
collects the generic on-site mul-apply lemmas and the case-1 / case-2 entry positivity and
vanishing lemmas.

The strict-positivity headline `spinSDotXXZSwap_apply_re_pos_of_raiseLowerStepS_witness` is kept in
the capstone module `AxisSwapBondReStrictPos.lean`.
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

end LatticeSystem.Quantum
