import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityGaugedSigns
import LatticeSystem.Quantum.SpinS.DressedAxisSwapSingleIonStrictPos

/-!
# Case (ii): local dressed signs

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file supplies the local sign layer for the case-(ii) parity-gauged PF
route.  It records exact `magSumS` changes for the two `±2` move types, proves
the local dressed real-entry signs for transverse, parity-bond, and single-ion
steps under the corresponding strict local hypotheses, and feeds those signs
into the structural sign-transfer API from
`AnisotropicHeisenbergSpinSCaseIIParityGaugedSigns`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Finite-sum bookkeeping -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- A finite sum of real numbers is strictly positive if every term is non-negative and at least
one term is strictly positive. -/
theorem Finset.sum_pos_of_forall_nonneg_of_exists_pos
    {α : Type*} {s : _root_.Finset α} {f : α → ℝ}
    (hnp : ∀ a ∈ s, 0 ≤ f a) (hex : ∃ a ∈ s, 0 < f a) : 0 < ∑ a ∈ s, f a := by
  classical
  obtain ⟨a₀, ha₀, hf₀⟩ := hex
  have hrest : 0 ≤ ∑ a ∈ s.erase a₀, f a :=
    _root_.Finset.sum_nonneg (fun a ha => hnp a (_root_.Finset.mem_of_mem_erase ha))
  calc 0
      < f a₀ + ∑ a ∈ s.erase a₀, f a := by linarith
    _ = ∑ a ∈ s, f a := by rw [_root_.Finset.add_sum_erase _ _ ha₀]

/-! ## Exact `magSumS` changes for local moves -/

omit [DecidableEq Λ] in
/-- If two configurations agree off one site `x`, their `magSumS` values differ only by the
local values at `x`.  The addition form avoids natural-number subtraction. -/
theorem magSumS_add_local_eq_of_agree_off_site
    {x : Λ} {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → σ' k = σ k) :
    magSumS σ' + (σ x).val = magSumS σ + (σ' x).val := by
  classical
  unfold magSumS
  have hx : x ∈ (Finset.univ : Finset Λ) := Finset.mem_univ x
  rw [← Finset.add_sum_erase _ (fun k => (σ' k).val) hx,
    ← Finset.add_sum_erase _ (fun k => (σ k).val) hx]
  have hrest :
      ∑ k ∈ Finset.univ.erase x, (σ' k).val =
        ∑ k ∈ Finset.univ.erase x, (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    exact congrArg Fin.val (h k (Finset.mem_erase.mp hk).1)
  rw [hrest]
  ring

omit [DecidableEq Λ] in
/-- If two configurations agree off two distinct sites `x` and `y`, their `magSumS` values differ
only by the two local values.  The addition form avoids natural-number subtraction. -/
theorem magSumS_add_local_two_eq_of_agree_off_two_site
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    magSumS σ' + ((σ x).val + (σ y).val) =
      magSumS σ + ((σ' x).val + (σ' y).val) := by
  classical
  unfold magSumS
  have hx : x ∈ (Finset.univ : Finset Λ) := Finset.mem_univ x
  have hy : y ∈ (Finset.univ.erase x : Finset Λ) :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  rw [← Finset.add_sum_erase _ (fun k => (σ' k).val) hx,
    ← Finset.add_sum_erase _ (fun k => (σ k).val) hx,
    ← Finset.add_sum_erase _ (fun k => (σ' k).val) hy,
    ← Finset.add_sum_erase _ (fun k => (σ k).val) hy]
  have hrest :
      ∑ k ∈ (Finset.univ.erase x).erase y, (σ' k).val =
        ∑ k ∈ (Finset.univ.erase x).erase y, (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkx : k ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
    have hky : k ≠ y := (Finset.mem_erase.mp hk).1
    exact congrArg Fin.val (h k hkx hky)
  rw [hrest]
  ring

omit [DecidableEq Λ] in
/-- A `SingleIonStepS` changes `magSumS` by exactly `+2` or `-2`. -/
theorem singleIonStepS_magSumS_add_two_or_add_two_magSumS
    {σ τ : Λ → Fin (N + 1)} (hstep : SingleIonStepS σ τ) :
    magSumS τ = magSumS σ + 2 ∨ magSumS τ + 2 = magSumS σ := by
  obtain ⟨x, hval, hagree⟩ := hstep
  have hsum := magSumS_add_local_eq_of_agree_off_site (x := x) hagree
  rcases hval with hraise | hlower
  · left
    omega
  · right
    omega

omit [DecidableEq Λ] in
/-- A `ParityBondStepS` changes `magSumS` by exactly `+2` or `-2`. -/
theorem parityBondStepS_magSumS_add_two_or_add_two_magSumS
    {G : SimpleGraph Λ} {σ τ : Λ → Fin (N + 1)}
    (hstep : ParityBondStepS G σ τ) :
    magSumS τ = magSumS σ + 2 ∨ magSumS τ + 2 = magSumS σ := by
  obtain ⟨x, y, hadj, hval, hagree⟩ := hstep
  have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hadj.ne hagree
  rcases hval with hraise | hlower
  · left
    omega
  · right
    omega

/-! ## Two-site parity-bond local ingredients -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- If two configurations differ at exactly the two distinct sites `x` and `y` and agree off
`a,b`, then `{a,b}` must be `{x,y}`. -/
theorem pair_or_swap_of_agree_off_two_site_two_diff
    {x y a b : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (hx : σ' x ≠ σ x) (hy : σ' y ≠ σ y)
    (hagree : ∀ k, k ≠ a → k ≠ b → σ' k = σ k) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  have hx_ab : x = a ∨ x = b := by
    by_cases hxa : x = a
    · exact Or.inl hxa
    · by_cases hxb : x = b
      · exact Or.inr hxb
      · exact (hx (hagree x hxa hxb)).elim
  have hy_ab : y = a ∨ y = b := by
    by_cases hya : y = a
    · exact Or.inl hya
    · by_cases hyb : y = b
      · exact Or.inr hyb
      · exact (hy (hagree y hya hyb)).elim
  rcases hx_ab with hxa | hxb <;> rcases hy_ab with hya | hyb
  · exact (hxy (hxa.trans hya.symm)).elim
  · exact Or.inl ⟨hxa.symm, hyb.symm⟩
  · exact Or.inr ⟨hya.symm, hxb.symm⟩
  · exact (hxy (hxb.trans hyb.symm)).elim

/-- The axis-swapped single-ion term vanishes when two distinct sites both change. -/
theorem singleIonAnisotropyS2_apply_eq_zero_of_two_site_diff
    {x y : Λ} (hxy : x ≠ y) {D : ℂ} {σ' σ : Λ → Fin (N + 1)}
    (hx : σ' x ≠ σ x) (hy : σ' y ≠ σ y) :
    singleIonAnisotropyS2 D N σ' σ = 0 := by
  rw [singleIonAnisotropyS2,
    show (∑ z : Λ, onSiteS z (spinSOp2 N) * onSiteS z (spinSOp2 N) : ManyBodyOpS Λ N) =
      ∑ z : Λ, onSiteS z (spinSOp2 N * spinSOp2 N) from
      Finset.sum_congr rfl (fun z _ => onSiteS_mul_onSiteS_same z _ _),
    Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  have hsum : ∑ z : Λ, (onSiteS z (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ = 0 := by
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hzx : z = x
    · subst z
      exact onSiteS_apply_eq_zero_of_off_site_diff x (spinSOp2 N * spinSOp2 N)
        (fun h => hy (h y hxy.symm))
    · exact onSiteS_apply_eq_zero_of_off_site_diff z (spinSOp2 N * spinSOp2 N)
        (fun h => hx (h x (Ne.symm hzx)))
  rw [hsum, mul_zero]

/-- In case (ii), the bare axis-swapped bond entry is strictly negative on a parity-bond
witness because `(1 - lambda.re) / 4` is strictly negative. -/
theorem spinSDotXXZSwap_apply_re_neg_of_parityBondStepS_witness_caseII
    {x y : Λ} (hxy : x ≠ y) {lam : ℂ}
    (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (spinSDotXXZSwap x y lam N σ' σ).re < 0 := by
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
  have hcoef2 : (1 - lam.re) / 4 < 0 := by linarith
  rcases hsh with ⟨hsx, hsy⟩ | ⟨hsx, hsy⟩
  · have h1 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) :
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
    exact mul_neg_of_neg_of_pos hcoef2 h4
  · have h1 : ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) :
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
    exact mul_neg_of_neg_of_pos hcoef2 h3

omit [DecidableEq Λ] in
/-- Marshall dressing flips a real strictly-negative entry to strictly-positive across a bipartite
bond with `A`-site at `x`. -/
theorem dressed_entry_re_pos_bipartite_x_of_re_neg
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hxod : Odd ((σ' x).val + (σ x).val))
    {z : ℂ} (hz : z.re < 0) :
    0 < (marshallSignS A σ * marshallSignS A σ' * z).re := by
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'),
    marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h hxod,
    neg_one_mul, Complex.neg_re]
  linarith

omit [DecidableEq Λ] in
/-- Marshall dressing flips a real strictly-negative entry to strictly-positive across a bipartite
bond with `A`-site at `y`. -/
theorem dressed_entry_re_pos_bipartite_y_of_re_neg
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hyod : Odd ((σ' y).val + (σ y).val))
    {z : ℂ} (hz : z.re < 0) :
    0 < (marshallSignS A σ * marshallSignS A σ' * z).re := by
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'),
    marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h hyod,
    neg_one_mul, Complex.neg_re]
  linarith

/-- In case (ii), the dressed bond entry is strictly positive on a parity-bond witness when the
`A`-site is `x`. -/
theorem dressedAxisSwapped_bond_re_pos_bipartite_x_of_parityBond_witness_caseII
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {lam : ℂ} (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re := by
  have hneg := spinSDotXXZSwap_apply_re_neg_of_parityBondStepS_witness_caseII
    hxy hlam hlam_gt hsh h
  have hxod : Odd ((σ' x).val + (σ x).val) := by
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [Nat.odd_iff]; omega
  exact dressed_entry_re_pos_bipartite_x_of_re_neg A hxy hAx hAy h hxod hneg

/-- In case (ii), the dressed bond entry is strictly positive on a parity-bond witness when the
`A`-site is `y`. -/
theorem dressedAxisSwapped_bond_re_pos_bipartite_y_of_parityBond_witness_caseII
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {lam : ℂ} (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re := by
  have hneg := spinSDotXXZSwap_apply_re_neg_of_parityBondStepS_witness_caseII
    hxy hlam hlam_gt hsh h
  have hyod : Odd ((σ' y).val + (σ y).val) := by
    rcases hsh with ⟨_, hsy⟩ | ⟨_, hsy⟩ <;> · rw [Nat.odd_iff]; omega
  exact dressed_entry_re_pos_bipartite_y_of_re_neg A hxy hAx hAy h hyod hneg

/-- In case (ii), the Marshall-dressed `Ĥ'` real entry is strictly positive on a
`ParityBondStepS` witness.  Non-witness bond terms vanish; the two oriented witness bonds are
non-negative, and the `(x,y)` contribution is strict. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_re_pos_of_parityBondStepS_witness_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {D : ℂ}
    {x y : Λ} (hxy : x ≠ y) (hAne : A x ≠ A y) (hJpos_xy : 0 < (J x y).re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re := by
  have hx_ne : σ' x ≠ σ x := by
    intro h
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [h] at hsx; omega
  have hy_ne : σ' y ≠ σ y := by
    intro h
    rcases hsh with ⟨_, hsy⟩ | ⟨_, hsy⟩ <;> · rw [h] at hsy; omega
  have hsh_yx :
      ((σ y).val + 1 = (σ' y).val ∧ (σ x).val + 1 = (σ' x).val) ∨
        ((σ' y).val + 1 = (σ y).val ∧ (σ' x).val + 1 = (σ x).val) := by
    rcases hsh with ⟨hsx, hsy⟩ | ⟨hsx, hsy⟩
    · exact Or.inl ⟨hsy, hsx⟩
    · exact Or.inr ⟨hsy, hsx⟩
  have hagree_yx : ∀ k, k ≠ y → k ≠ x → σ' k = σ k := fun k hky hkx => hagree k hkx hky
  have hbond_xy_pos :
      0 < (marshallSignS A σ * marshallSignS A σ' *
        (J x y * spinSDotXXZSwap x y lam N σ' σ)).re := by
    rw [show marshallSignS A σ * marshallSignS A σ' *
          (J x y * spinSDotXXZSwap x y lam N σ' σ) =
        J x y * (marshallSignS A σ * marshallSignS A σ' *
          spinSDotXXZSwap x y lam N σ' σ) from by ring,
      Complex.mul_re, hJim, zero_mul, sub_zero]
    have hbase :
        0 < (marshallSignS A σ * marshallSignS A σ' *
          spinSDotXXZSwap x y lam N σ' σ).re := by
      rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
      · have hAy : A y = false := by
          rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
          · exact absurd (hAx.trans hAy.symm) hAne
          · exact hAy
        exact dressedAxisSwapped_bond_re_pos_bipartite_x_of_parityBond_witness_caseII
          A hxy hAx hAy hlam hlam_gt hsh hagree
      · have hAy : A y = true := by
          rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
          · exact hAy
          · exact absurd (hAx.trans hAy.symm) hAne
        exact dressedAxisSwapped_bond_re_pos_bipartite_y_of_parityBond_witness_caseII
          A hxy hAx hAy hlam hlam_gt hsh hagree
    exact mul_pos hJpos_xy hbase
  have hbond_nonneg : ∀ a b, 0 ≤ (marshallSignS A σ * marshallSignS A σ' *
      (J a b * spinSDotXXZSwap a b lam N σ' σ)).re := by
    intro a b
    by_cases hab : a = b
    · subst a
      rw [hJself b, zero_mul, mul_zero, Complex.zero_re]
    · by_cases hagree_ab : ∀ k, k ≠ a → k ≠ b → σ' k = σ k
      · have hpair := pair_or_swap_of_agree_off_two_site_two_diff hxy hx_ne hy_ne hagree_ab
        rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · subst a
          subst b
          exact le_of_lt hbond_xy_pos
        · subst a
          subst b
          rw [show marshallSignS A σ * marshallSignS A σ' *
                (J y x * spinSDotXXZSwap y x lam N σ' σ) =
              J y x * (marshallSignS A σ * marshallSignS A σ' *
                spinSDotXXZSwap y x lam N σ' σ) from by ring,
            Complex.mul_re, hJim, zero_mul, sub_zero]
          have hbase :
              0 < (marshallSignS A σ * marshallSignS A σ' *
                spinSDotXXZSwap y x lam N σ' σ).re := by
            rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
            · have hAx : A x = false := by
                rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
                · exact absurd (hAy.trans hAx.symm) hAne.symm
                · exact hAx
              exact dressedAxisSwapped_bond_re_pos_bipartite_x_of_parityBond_witness_caseII
                A hxy.symm hAy hAx hlam hlam_gt hsh_yx hagree_yx
            · have hAx : A x = true := by
                rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
                · exact hAx
                · exact absurd (hAy.trans hAx.symm) hAne.symm
              exact dressedAxisSwapped_bond_re_pos_bipartite_y_of_parityBond_witness_caseII
                A hxy.symm hAy hAx hlam hlam_gt hsh_yx hagree_yx
          exact mul_nonneg (hJnn y x) (le_of_lt hbase)
      · rw [spinSDotXXZSwap_apply_eq_zero_of_not_agree hab lam hagree_ab,
          mul_zero, mul_zero, Complex.zero_re]
  have hsum : (∑ a : Λ, ∑ b : Λ, J a b • spinSDotXXZSwap a b lam N : ManyBodyOpS Λ N) σ' σ =
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  have hsingle_zero :
      (marshallSignS A σ * marshallSignS A σ' * singleIonAnisotropyS2 D N σ' σ).re = 0 := by
    rw [singleIonAnisotropyS2_apply_eq_zero_of_two_site_diff hxy hx_ne hy_ne, mul_zero,
      Complex.zero_re]
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
    mul_comm (marshallSignS A σ') (marshallSignS A σ),
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hsum, mul_add, Complex.add_re]
  have hbonds_pos : 0 < (marshallSignS A σ * marshallSignS A σ' *
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_pos_of_forall_nonneg_of_exists_pos
    · intro a _
      rw [Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_nonneg (fun b _ => hbond_nonneg a b)
    · refine ⟨x, Finset.mem_univ x, ?_⟩
      rw [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_pos_of_forall_nonneg_of_exists_pos
      · intro b _; exact hbond_nonneg x b
      · exact ⟨y, Finset.mem_univ y, hbond_xy_pos⟩
  linarith

/-- In case (ii), the real-part matrix entry is strictly positive on a `ParityBondStepS`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_pos_of_parityBondStepS_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {D : ℂ}
    {σ τ : Λ → Fin (N + 1)}
    (hstep : ParityBondStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ σ := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := hstep
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply]
  exact dressedAxisSwappedAnisotropicHeisenbergS_apply_re_pos_of_parityBondStepS_witness_caseII
    A hJim hJnn hJself hlam hlam_gt hadj.ne
    (bipartiteCompleteGraphOf_adj_sublattice_ne hadj) (hJpos x y hadj) hsh hagree

/-- In case (ii), a parity-bond `±2` move gives a strictly positive off-diagonal entry of the
parity-gauged shifted matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_parityBondStepS
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {D : ℂ}
    (c : ℝ) {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hstep : ParityBondStepS (bipartiteCompleteGraphOf A) σ.1 τ.1) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  have hcfg_ne : τ.1 ≠ σ.1 := by
    obtain ⟨x, _y, _hadj, hsh, _hagree⟩ := hstep
    intro heq
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [heq] at hsx; omega
  have hne : τ ≠ σ := by
    intro h
    exact hcfg_ne (congrArg Subtype.val h)
  have hmag := parityBondStepS_magSumS_add_two_or_add_two_magSumS hstep
  have hentry :
      0 < dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_pos_of_parityBondStepS_caseII
      A hJim hJnn hJpos hJself hlam hlam_gt hstep
  rcases hmag with hmag | hmag
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_add_two
      A J lam D N c hne hmag hentry
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_add_two_magSumS
      A J lam D N c hne hmag hentry

/-! ## Transverse case-II shifted-entry positivity -/

/-- In case (ii), the Marshall-dressed `Ĥ'` real entry is strictly negative on a transverse
`RaiseLowerStepS` witness.  The single-ion part vanishes because two distinct sites change. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {D : ℂ}
    {x y : Λ} (hxy : x ≠ y) (hAne : A x ≠ A y) (hJpos_xy : 0 < (J x y).re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re < 0 := by
  have hx_ne : σ' x ≠ σ x := by
    intro h
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [h] at hsx; omega
  have hy_ne : σ' y ≠ σ y := by
    intro h
    rcases hsh with ⟨_, hsy⟩ | ⟨_, hsy⟩ <;> · rw [h] at hsy; omega
  have hsh_yx :
      ((σ y).val + 1 = (σ' y).val ∧ (σ' x).val + 1 = (σ x).val) ∨
        ((σ' y).val + 1 = (σ y).val ∧ (σ x).val + 1 = (σ' x).val) := by
    rcases hsh with ⟨hsx, hsy⟩ | ⟨hsx, hsy⟩
    · exact Or.inr ⟨hsy, hsx⟩
    · exact Or.inl ⟨hsy, hsx⟩
  have hagree_yx : ∀ k, k ≠ y → k ≠ x → σ' k = σ k := fun k hky hkx => hagree k hkx hky
  have hbond_xy_neg : (marshallSignS A σ * marshallSignS A σ' *
      (J x y * spinSDotXXZSwap x y lam N σ' σ)).re < 0 := by
    rw [show marshallSignS A σ * marshallSignS A σ' *
          (J x y * spinSDotXXZSwap x y lam N σ' σ) =
        J x y * (marshallSignS A σ * marshallSignS A σ' *
          spinSDotXXZSwap x y lam N σ' σ) from by ring,
      Complex.mul_re, hJim, zero_mul, sub_zero]
    have hbase :
        (marshallSignS A σ * marshallSignS A σ' *
          spinSDotXXZSwap x y lam N σ' σ).re < 0 := by
      rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
      · have hAy : A y = false := by
          rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
          · exact absurd (hAx.trans hAy.symm) hAne
          · exact hAy
        exact dressedAxisSwapped_bond_re_neg_bipartite_x_of_raiseLower_witness
          A hxy hAx hAy hlam hlb hsh hagree
      · have hAy : A y = true := by
          rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
          · exact hAy
          · exact absurd (hAx.trans hAy.symm) hAne
        exact dressedAxisSwapped_bond_re_neg_bipartite_y_of_raiseLower_witness
          A hxy hAx hAy hlam hlb hsh hagree
    exact mul_neg_of_pos_of_neg hJpos_xy hbase
  have hbond_nonpos : ∀ a b, (marshallSignS A σ * marshallSignS A σ' *
      (J a b * spinSDotXXZSwap a b lam N σ' σ)).re ≤ 0 := by
    intro a b
    by_cases hab : a = b
    · subst a
      rw [hJself b, zero_mul, mul_zero, Complex.zero_re]
    · by_cases hagree_ab : ∀ k, k ≠ a → k ≠ b → σ' k = σ k
      · have hpair := pair_or_swap_of_agree_off_two_site_two_diff hxy hx_ne hy_ne hagree_ab
        rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · subst a
          subst b
          exact le_of_lt hbond_xy_neg
        · subst a
          subst b
          rw [show marshallSignS A σ * marshallSignS A σ' *
                (J y x * spinSDotXXZSwap y x lam N σ' σ) =
              J y x * (marshallSignS A σ * marshallSignS A σ' *
                spinSDotXXZSwap y x lam N σ' σ) from by ring,
            Complex.mul_re, hJim, zero_mul, sub_zero]
          have hbase :
              (marshallSignS A σ * marshallSignS A σ' *
                spinSDotXXZSwap y x lam N σ' σ).re < 0 := by
            rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
            · have hAx : A x = false := by
                rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
                · exact absurd (hAy.trans hAx.symm) hAne.symm
                · exact hAx
              exact dressedAxisSwapped_bond_re_neg_bipartite_x_of_raiseLower_witness
                A hxy.symm hAy hAx hlam hlb hsh_yx hagree_yx
            · have hAx : A x = true := by
                rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
                · exact hAx
                · exact absurd (hAy.trans hAx.symm) hAne.symm
              exact dressedAxisSwapped_bond_re_neg_bipartite_y_of_raiseLower_witness
                A hxy.symm hAy hAx hlam hlb hsh_yx hagree_yx
          exact mul_nonpos_of_nonneg_of_nonpos (hJnn y x) (le_of_lt hbase)
      · rw [spinSDotXXZSwap_apply_eq_zero_of_not_agree hab lam hagree_ab,
          mul_zero, mul_zero, Complex.zero_re]
  have hsum : (∑ a : Λ, ∑ b : Λ, J a b • spinSDotXXZSwap a b lam N : ManyBodyOpS Λ N) σ' σ =
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  have hsingle_zero :
      (marshallSignS A σ * marshallSignS A σ' * singleIonAnisotropyS2 D N σ' σ).re = 0 := by
    rw [singleIonAnisotropyS2_apply_eq_zero_of_two_site_diff hxy hx_ne hy_ne, mul_zero,
      Complex.zero_re]
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
  linarith

/-- In case (ii), the real-part matrix entry is strictly negative on a transverse
`RaiseLowerStepS`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {D : ℂ}
    {σ τ : Λ → Fin (N + 1)}
    (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ τ) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ σ < 0 := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := hstep
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply]
  exact dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness_caseII
    A hJim hJnn hJself hlam hlb hadj.ne
    (bipartiteCompleteGraphOf_adj_sublattice_ne hadj) (hJpos x y hadj) hsh hagree

/-- In case (ii), a transverse `RaiseLowerStepS` gives a strictly positive off-diagonal entry of
the parity-gauged shifted matrix.  The extra parity gauge is neutral because `magSumS` is
preserved. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_raiseLowerStepS
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {D : ℂ}
    (c : ℝ) {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ.1 τ.1) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  have hcfg_ne : τ.1 ≠ σ.1 := by
    obtain ⟨x, _y, _hadj, hsh, _hagree⟩ := hstep
    intro heq
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [heq] at hsx; omega
  have hne : τ ≠ σ := by
    intro h
    exact hcfg_ne (congrArg Subtype.val h)
  have hmag : magSumS τ.1 = magSumS σ.1 := magSumS_eq_of_raiseLowerStepS hstep
  have hentry :
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 < 0 :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_caseII
      A hJim hJnn hJpos hJself hlam hlb hstep
  exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_eq
    A J lam D N c hne hmag hentry

/-! ## Single-ion case-II shifted-entry positivity -/

/-- In case (ii), the Marshall-dressed `Ĥ'` real entry is strictly positive on a same-site
`±2` move.  The bond part vanishes as in the case-(i.2) proof, while the axis-swapped single-ion
entry is strictly negative before multiplication by the strictly negative crystal field. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_re_pos_of_singleIonStepS_witness_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {x : Λ}
    {σ' σ : Λ → Fin (N + 1)}
    (hsx : (σ x).val + 2 = (σ' x).val ∨ (σ' x).val + 2 = (σ x).val)
    (hagree : ∀ k, k ≠ x → σ' k = σ k) :
    0 < (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re := by
  have hbonds_zero :
      (marshallSignS A σ * marshallSignS A σ' *
        (∑ a : Λ, ∑ b : Λ, J a b • spinSDotXXZSwap a b lam N : ManyBodyOpS Λ N) σ' σ).re = 0 := by
    rw [Matrix.sum_apply]
    have h_inner : ∀ a, (∑ b : Λ, J a b • spinSDotXXZSwap a b lam N) σ' σ = 0 := by
      intro a
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul]
      by_cases hab : a = b
      · subst hab; rw [hJself a, zero_mul]
      · rw [spinSDotXXZSwap_apply_eq_zero_of_singleIonStep hab lam hsx hagree, mul_zero]
    rw [Finset.sum_eq_zero (fun a _ => h_inner a), mul_zero, Complex.zero_re]
  have hsingle_re :
      0 < (marshallSignS A σ * marshallSignS A σ' * singleIonAnisotropyS2 D N σ' σ).re := by
    rw [singleIonAnisotropyS2,
      show (∑ y : Λ, onSiteS y (spinSOp2 N) * onSiteS y (spinSOp2 N) : ManyBodyOpS Λ N) =
        ∑ y : Λ, onSiteS y (spinSOp2 N * spinSOp2 N) from
        Finset.sum_congr rfl (fun y _ => onSiteS_mul_onSiteS_same y _ _),
      Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    have hsum_eq : ∑ y : Λ, (onSiteS y (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ =
        (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
      have hrest : ∑ y ∈ Finset.univ.erase x, (onSiteS y (spinSOp2 N * spinSOp2 N) :
          ManyBodyOpS Λ N) σ' σ = 0 := by
        refine Finset.sum_eq_zero (fun y hy => ?_)
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        have hsx_ne : σ' x ≠ σ x := by
          intro h
          rcases hsx with hh | hh <;> · rw [h] at hh; omega
        exact onSiteS_spinSOp2_sq_apply_eq_zero_of_singleIon_off_site hsx_ne hyx
      rw [hrest, add_zero]
    rw [hsum_eq]
    rw [show marshallSignS A σ * marshallSignS A σ' * (D *
          (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ) =
        D * (marshallSignS A σ * marshallSignS A σ' *
          (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ) from by ring,
      Complex.mul_re, hDim, zero_mul, sub_zero]
    exact mul_pos_of_neg_of_neg hDneg
      (dressed_onSiteS_spinSOp2_sq_re_neg_of_singleIon_witness A hsx hagree)
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
    mul_comm (marshallSignS A σ') (marshallSignS A σ),
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, mul_add, Complex.add_re]
  linarith

/-- In case (ii), the real-part matrix entry is strictly positive on a same-site `±2` move. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_pos_of_singleIonStepS_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {σ τ : Λ → Fin (N + 1)} (hstep : SingleIonStepS σ τ) :
    0 < dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ σ := by
  obtain ⟨x, hsx, hagree⟩ := hstep
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply]
  exact dressedAxisSwappedAnisotropicHeisenbergS_apply_re_pos_of_singleIonStepS_witness_caseII
    A hJself hDim hDneg hsx hagree

/-- In case (ii), a same-site `±2` move gives a strictly positive off-diagonal entry of the
parity-gauged shifted matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_singleIonStepS
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    (c : ℝ) {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hstep : SingleIonStepS σ.1 τ.1) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  have hcfg_ne : τ.1 ≠ σ.1 := by
    obtain ⟨x, hsx, _hagree⟩ := hstep
    intro heq
    rcases hsx with hsx | hsx <;> · rw [heq] at hsx; omega
  have hne : τ ≠ σ := by
    intro h
    exact hcfg_ne (congrArg Subtype.val h)
  have hmag := singleIonStepS_magSumS_add_two_or_add_two_magSumS hstep
  have hentry :
      0 < dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_pos_of_singleIonStepS_caseII
      A hJself hDim hDneg hstep
  rcases hmag with hmag | hmag
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_add_two
      A J lam D N c hne hmag hentry
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_add_two_magSumS
      A J lam D N c hne hmag hentry

end LatticeSystem.Quantum
