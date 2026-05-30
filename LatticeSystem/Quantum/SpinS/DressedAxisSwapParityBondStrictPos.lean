import LatticeSystem.Quantum.SpinS.AxisSwapBondReStrictPos
import LatticeSystem.Quantum.SpinS.DressedAxisSwapRaiseLowerStrictNeg
import LatticeSystem.Quantum.SpinS.ParityReachable

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Strict positivity of the shifted PF matrix on a bond parity step (case (i) strict²)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a `ParityBondStepS` witness on `bipartiteCompleteGraphOf A` (both endpoints of a bond shifted
in the *same* Fin direction by `±1`), under case (i) strict² (`−1 < λ.re < 1` real, `D.re ≥ 0`),
the shifted PF matrix entry `shiftedDressedAxisSwappedReMatrix τ σ > 0`.

Parallels the transverse step (#3790–#3792) with the parity ladder pair replacing the transverse
ladder pair:

* The matching parity ladder product (`Ŝ⁻_x Ŝ⁻_y` for the both-raised case, `Ŝ⁺_x Ŝ⁺_y` for the
  both-lowered case) gives a strict positive real factor at both sites.
* The off-direction parity hop and both transverse terms vanish by Fin-index mismatch.
* Coefficient `(1 − λ.re)/4 > 0` strict from `λ.re < 1`.
* Marshall A-site flip yields dressed Re strict negative; shifted off-diag = `−dressed.re > 0`.

This is the `hB_step` of `Matrix.isIrreducible_iff_exists_pow_pos` for the bond-parity `±2`-move in
PR5 (parity-block Perron–Frobenius irreducibility).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Bond core: `spinSDotXXZSwap` strict positive real on a `ParityBondStepS` witness. -/

/-- Case 1 (both Fin indices `+1`): the parity ladder `Ŝ⁻_x Ŝ⁻_y` matches and gives strict
positive real part at both sites. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_re_pos_parityBond_case1
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 1 = (σ' x).val) (hsy : (σ y).val + 1 = (σ' y).val)
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
    Complex.mul_re, spinSOpMinus_apply_im_zero, spinSOpMinus_apply_im_zero, mul_zero, sub_zero]
  exact mul_pos (spinSOpMinus_apply_re_pos_of_lower N hsx)
    (spinSOpMinus_apply_re_pos_of_lower N hsy)

/-- Case 2 (both Fin indices `−1`): the parity ladder `Ŝ⁺_x Ŝ⁺_y` matches and gives strict
positive real part at both sites. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_re_pos_parityBond_case2
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ' x).val + 1 = (σ x).val) (hsy : (σ' y).val + 1 = (σ y).val)
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
    Complex.mul_re, spinSOpPlus_apply_im_zero, spinSOpPlus_apply_im_zero, mul_zero, sub_zero]
  exact mul_pos (spinSOpPlus_apply_re_pos_of_raise N hsx)
    (spinSOpPlus_apply_re_pos_of_raise N hsy)

/-- **Strict positivity of the axis-swapped bond entry on a parity-bond witness** (case (i)
strict²).  For `−1 < λ.re < 1` real and a `ParityBondStepS` witness on `{x, y}`,
`Re(spinSDotXXZSwap x y λ N σ' σ) > 0`. -/
theorem spinSDotXXZSwap_apply_re_pos_of_parityBondStepS_witness
    {x y : Λ} (hxy : x ≠ y) {lam : ℂ}
    (hlam : lam.im = 0) (hub : lam.re < 1)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
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
  have hcoef2 : 0 < (1 - lam.re) / 4 := by linarith
  rcases hsh with ⟨hsx, hsy⟩ | ⟨hsx, hsy⟩
  · -- Case 1: matching = Minus_x * Minus_y; transverse + Plus*Plus vanish.
    have h1 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
        spinSOpPlus_apply_other N (by omega : (σ' x).val + 1 ≠ (σ x).val), zero_mul,
        Complex.zero_re]
    have h2 : ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
        spinSOpPlus_apply_other N (by omega : (σ' y).val + 1 ≠ (σ y).val), mul_zero,
        Complex.zero_re]
    have h3 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
        spinSOpPlus_apply_other N (by omega : (σ' x).val + 1 ≠ (σ x).val), zero_mul,
        Complex.zero_re]
    have h4 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_re_pos_parityBond_case1
      hxy hsx hsy hagree
    rw [h1, h2, h3]
    simp only [add_zero, zero_add, mul_zero]
    exact mul_pos hcoef2 h4
  · -- Case 2: matching = Plus_x * Plus_y; transverse + Minus*Minus vanish.
    have h1 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
        spinSOpMinus_apply_other N (by omega : (σ y).val + 1 ≠ (σ' y).val), mul_zero,
        Complex.zero_re]
    have h2 : ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy hagree,
        spinSOpMinus_apply_other N (by omega : (σ x).val + 1 ≠ (σ' x).val), zero_mul,
        Complex.zero_re]
    have h3 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_re_pos_parityBond_case2
      hxy hsx hsy hagree
    have h4 : ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N) :
        ManyBodyOpS Λ N) σ' σ).re = 0 := by
      rw [onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
        spinSOpMinus_apply_other N (by omega : (σ x).val + 1 ≠ (σ' x).val), zero_mul,
        Complex.zero_re]
    rw [h1, h2, h4]
    simp only [add_zero, zero_add, mul_zero]
    exact mul_pos hcoef2 h3

/-! ## Dressed bond strict negative on a parity-bond witness. -/

/-- Strict negativity of the dressed bond on a parity-bond witness, A-site at `x`. -/
theorem dressedAxisSwapped_bond_re_neg_bipartite_x_of_parityBond_witness
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {lam : ℂ} (hlam : lam.im = 0) (hub : lam.re < 1)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re < 0 := by
  have hzp := spinSDotXXZSwap_apply_re_pos_of_parityBondStepS_witness hxy hlam hub hsh h
  have hxod : Odd ((σ' x).val + (σ x).val) := by
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [Nat.odd_iff]; omega
  exact dressed_entry_re_neg_bipartite_x A hxy hAx hAy h hxod hzp

/-- Strict negativity of the dressed bond on a parity-bond witness, A-site at `y`. -/
theorem dressedAxisSwapped_bond_re_neg_bipartite_y_of_parityBond_witness
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {lam : ℂ} (hlam : lam.im = 0) (hub : lam.re < 1)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re < 0 := by
  have hzp := spinSDotXXZSwap_apply_re_pos_of_parityBondStepS_witness hxy hlam hub hsh h
  have hyod : Odd ((σ' y).val + (σ y).val) := by
    rcases hsh with ⟨_, hsy⟩ | ⟨_, hsy⟩ <;> · rw [Nat.odd_iff]; omega
  exact dressed_entry_re_neg_bipartite_y A hxy hAx hAy h hyod hzp

/-! ## Full Ĥ' strict negativity + shifted strict positivity. -/

/-- **Strict negativity of the dressed `Ĥ'` off-diagonal on a `ParityBondStepS` witness** (case (i)
strict²). -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_parityBondStepS_witness_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {x y : Λ} (hxy : x ≠ y) (hAne : A x ≠ A y)
    (hJpos_xy : 0 < (J x y).re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re < 0 := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [he] at hsx; omega
  -- Per-bond dressed contribution Re ≤ 0 (existing #3770).
  have hbond_nonpos : ∀ a b, (marshallSignS A σ * marshallSignS A σ' *
      (J a b * spinSDotXXZSwap a b lam N σ' σ)).re ≤ 0 := by
    intro a b
    by_cases hJ : J a b = 0
    · rw [hJ, zero_mul, mul_zero, Complex.zero_re]
    · have hAxy := hJbip a b hJ
      have hxy_ab : a ≠ b := fun h => hJ (by rw [h]; exact hJself b)
      by_cases hagree_ab : ∀ k, k ≠ a → k ≠ b → σ' k = σ k
      · have hz : (marshallSignS A σ * marshallSignS A σ' *
            spinSDotXXZSwap a b lam N σ' σ).re ≤ 0 := by
          rcases Bool.eq_false_or_eq_true (A a) with hAa | hAa
          · have hAb : A b = false := by
              rcases Bool.eq_false_or_eq_true (A b) with hAb | hAb
              · exact absurd (hAa.trans hAb.symm) hAxy
              · exact hAb
            exact dressedAxisSwapped_bond_re_nonpos_bipartite_x A hxy_ab hAa hAb hlam
              (le_of_lt hlb) (le_of_lt hub) hne hagree_ab
          · have hAb : A b = true := by
              rcases Bool.eq_false_or_eq_true (A b) with hAb | hAb
              · exact hAb
              · exact absurd (hAa.trans hAb.symm) hAxy
            exact dressedAxisSwapped_bond_re_nonpos_bipartite_y A hxy_ab hAa hAb hlam
              (le_of_lt hlb) (le_of_lt hub) hne hagree_ab
        rw [show marshallSignS A σ * marshallSignS A σ' *
              (J a b * spinSDotXXZSwap a b lam N σ' σ) =
            J a b * (marshallSignS A σ * marshallSignS A σ' *
              spinSDotXXZSwap a b lam N σ' σ) from by ring,
          Complex.mul_re, hJim, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (hJnn a b) hz
      · rw [spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy_ab lam hagree_ab,
          mul_zero, mul_zero, Complex.zero_re]
  -- Strict negativity of the (x, y) bond contribution.
  have hbond_xy_neg : (marshallSignS A σ * marshallSignS A σ' *
      (J x y * spinSDotXXZSwap x y lam N σ' σ)).re < 0 := by
    rw [show marshallSignS A σ * marshallSignS A σ' * (J x y * spinSDotXXZSwap x y lam N σ' σ)
        = J x y * (marshallSignS A σ * marshallSignS A σ' *
          spinSDotXXZSwap x y lam N σ' σ) from by ring,
      Complex.mul_re, hJim, zero_mul, sub_zero]
    rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
    · have hAy : A y = false := by
        rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
        · exact absurd (hAx.trans hAy.symm) hAne
        · exact hAy
      have hbond := dressedAxisSwapped_bond_re_neg_bipartite_x_of_parityBond_witness A hxy hAx hAy
        hlam hub hsh hagree
      exact mul_neg_of_pos_of_neg hJpos_xy hbond
    · have hAy : A y = true := by
        rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
        · exact hAy
        · exact absurd (hAx.trans hAy.symm) hAne
      have hbond := dressedAxisSwapped_bond_re_neg_bipartite_y_of_parityBond_witness A hxy hAx hAy
        hlam hub hsh hagree
      exact mul_neg_of_pos_of_neg hJpos_xy hbond
  -- The bond-sum off-diagonal entry, pushed through the double sum.
  have hsum : (∑ a : Λ, ∑ b : Λ, J a b • spinSDotXXZSwap a b lam N : ManyBodyOpS Λ N) σ' σ =
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
    mul_comm (marshallSignS A σ') (marshallSignS A σ),
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hsum, mul_add, Complex.add_re]
  have hbonds_neg : (marshallSignS A σ * marshallSignS A σ' *
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ).re < 0 := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_neg_of_forall_nonpos_of_exists_neg
    · intro a _
      rw [Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_nonpos (fun b _ => hbond_nonpos a b)
    · refine ⟨x, Finset.mem_univ x, ?_⟩
      rw [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_neg_of_forall_nonpos_of_exists_neg
      · intro b _; exact hbond_nonpos x b
      · exact ⟨y, Finset.mem_univ y, hbond_xy_neg⟩
  exact add_neg_of_neg_of_nonpos hbonds_neg
    (dressed_singleIonAnisotropyS2_re_nonpos A hDim hDnn hne)

/-- The shifted PF matrix entry is strictly positive on a `ParityBondStepS` witness on a bipartite
bond (case (i) strict²). -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_witness_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {x y : Λ} (hxy : x ≠ y) (hAne : A x ≠ A y) (hJpos_xy : 0 < (J x y).re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c σ' σ := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [he] at hsx; omega
  unfold shiftedDressedAxisSwappedReMatrix
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, zero_sub]
  have hneg :=
    dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_parityBondStepS_witness_bipartite
      A hJim hJnn hJself hJbip hlam hlb hub hDim hDnn hxy hAne hJpos_xy hsh hagree
  show 0 < -((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N) σ' σ).re
  linarith

/-- **Shifted PF strictly positive on a `ParityBondStepS`**.  For a bond-parity move on
`bipartiteCompleteGraphOf A` under case (i) strict², the shifted matrix is strict positive. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : ParityBondStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := hstep
  have hxy : x ≠ y := hadj.ne
  have hAne : A x ≠ A y := bipartiteCompleteGraphOf_adj_sublattice_ne hadj
  exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_witness_bipartite
    A hJim hJnn hJself hJbip hlam hlb hub hDim hDnn c hxy hAne (hJpos x y hadj) hsh hagree

end LatticeSystem.Quantum
