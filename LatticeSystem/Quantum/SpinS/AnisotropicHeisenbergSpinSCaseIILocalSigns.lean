import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityGaugedSigns
import LatticeSystem.Quantum.SpinS.DressedAxisSwapSingleIonStrictPos
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIILocalSignsCore

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
