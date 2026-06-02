import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIStepSupport

/-!
# Case (ii): raw support classification for the parity-gauged block matrix

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file starts the raw support-classification layer for the case-(ii)
parity-gauged shifted block matrix.  It records the local zero tests used to
turn raw total-Hamiltonian entries into the step-or-zero hypotheses consumed by
`AnisotropicHeisenbergSpinSCaseIIStepSupport`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Local zero tests -/

/-- A same-site `(S^2)^2` entry vanishes off the diagonal unless the local
configuration changes by exactly two. -/
theorem onSiteS_spinSOp2_sq_apply_eq_zero_of_not_pm_two
    {x : Λ} {σ' σ : Λ → Fin (N + 1)}
    (hne : σ' ≠ σ)
    (hagree : ∀ k, k ≠ x → σ' k = σ k)
    (hraise : (σ x).val + 2 ≠ (σ' x).val)
    (hlower : (σ' x).val + 2 ≠ (σ x).val) :
    (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_apply, if_pos hagree]
  have hlocal : σ' x ≠ σ x := by
    intro hx
    apply hne
    funext k
    by_cases hk : k = x
    · rw [hk, hx]
    · exact hagree k hk
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hlocal]
  rw [spinSOpPlus_mul_spinSOpPlus_apply_eq_zero_of_ne N hlower,
    spinSOpMinus_mul_spinSOpMinus_apply_eq_zero_of_ne N hraise]
  ring

/-- The single-ion term vanishes on an off-diagonal pair unless the pair is a
`SingleIonStepS`. -/
theorem singleIonAnisotropyS2_apply_eq_zero_of_not_singleIonStepS
    (D : ℂ) (N : ℕ) {σ' σ : Λ → Fin (N + 1)}
    (hne : σ' ≠ σ) (hnot : ¬ SingleIonStepS σ σ') :
    singleIonAnisotropyS2 D N σ' σ = 0 := by
  rw [singleIonAnisotropyS2,
    show (∑ x : Λ, onSiteS x (spinSOp2 N) * onSiteS x (spinSOp2 N) : ManyBodyOpS Λ N) =
      ∑ x : Λ, onSiteS x (spinSOp2 N * spinSOp2 N) from
      Finset.sum_congr rfl (fun x _ => onSiteS_mul_onSiteS_same x _ _),
    Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  have hsum :
      (∑ x : Λ, (onSiteS x (spinSOp2 N * spinSOp2 N) : ManyBodyOpS Λ N) σ' σ) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hagree : ∀ k, k ≠ x → σ' k = σ k
    · by_cases hraise : (σ x).val + 2 = (σ' x).val
      · exact (hnot ⟨x, Or.inl hraise, hagree⟩).elim
      · by_cases hlower : (σ' x).val + 2 = (σ x).val
        · exact (hnot ⟨x, Or.inr hlower, hagree⟩).elim
        · exact onSiteS_spinSOp2_sq_apply_eq_zero_of_not_pm_two hne hagree hraise hlower
    · exact onSiteS_apply_eq_zero_of_off_site_diff x (spinSOp2 N * spinSOp2 N) hagree
  rw [hsum, mul_zero]

/-- On an equal-`magSumS` off-diagonal pair, a bond entry on an adjacent pair
vanishes unless the pair is a transverse `RaiseLowerStepS`. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_magSum_eq_not_raiseLowerStepS
    {G : SimpleGraph Λ} {x y : Λ} (hadj : G.Adj x y) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' = magSumS σ)
    (hnot : ¬ RaiseLowerStepS G σ σ') :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hxy : x ≠ y := hadj.ne
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · by_cases hxr : (σ x).val + 1 = (σ' x).val
    · by_cases hyr : (σ y).val + 1 = (σ' y).val
      · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
        exfalso
        omega
      · by_cases hyl : (σ' y).val + 1 = (σ y).val
        · exact (hnot ⟨x, y, hadj, Or.inl ⟨hxr, hyl⟩, hagree⟩).elim
        · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
    · by_cases hxl : (σ' x).val + 1 = (σ x).val
      · by_cases hyr : (σ y).val + 1 = (σ' y).val
        · exact (hnot ⟨x, y, hadj, Or.inr ⟨hxl, hyr⟩, hagree⟩).elim
        · by_cases hyl : (σ' y).val + 1 = (σ y).val
          · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
            exfalso
            omega
          · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
      · exact spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1 hxy lam hne hxr hxl
  · exact spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy lam hagree

/-- On a target-raised-by-two off-diagonal pair, a bond entry on an adjacent
pair vanishes unless the pair is a `ParityBondStepS`. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_magSum_add_two_not_parityBondStepS
    {G : SimpleGraph Λ} {x y : Λ} (hadj : G.Adj x y) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' = magSumS σ + 2)
    (hnot : ¬ ParityBondStepS G σ σ') :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hxy : x ≠ y := hadj.ne
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · by_cases hxr : (σ x).val + 1 = (σ' x).val
    · by_cases hyr : (σ y).val + 1 = (σ' y).val
      · exact (hnot ⟨x, y, hadj, Or.inl ⟨hxr, hyr⟩, hagree⟩).elim
      · by_cases hyl : (σ' y).val + 1 = (σ y).val
        · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
          exfalso
          omega
        · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
    · by_cases hxl : (σ' x).val + 1 = (σ x).val
      · by_cases hyr : (σ y).val + 1 = (σ' y).val
        · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
          exfalso
          omega
        · by_cases hyl : (σ' y).val + 1 = (σ y).val
          · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
            exfalso
            omega
          · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
      · exact spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1 hxy lam hne hxr hxl
  · exact spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy lam hagree

/-- On a source-raised-by-two off-diagonal pair, a bond entry on an adjacent
pair vanishes unless the pair is a `ParityBondStepS`. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_add_two_magSum_not_parityBondStepS
    {G : SimpleGraph Λ} {x y : Λ} (hadj : G.Adj x y) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' + 2 = magSumS σ)
    (hnot : ¬ ParityBondStepS G σ σ') :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hxy : x ≠ y := hadj.ne
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · by_cases hxr : (σ x).val + 1 = (σ' x).val
    · by_cases hyr : (σ y).val + 1 = (σ' y).val
      · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
        exfalso
        omega
      · by_cases hyl : (σ' y).val + 1 = (σ y).val
        · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
          exfalso
          omega
        · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
    · by_cases hxl : (σ' x).val + 1 = (σ x).val
      · by_cases hyr : (σ y).val + 1 = (σ' y).val
        · have hsum := magSumS_add_local_two_eq_of_agree_off_two_site hxy hagree
          exfalso
          omega
        · by_cases hyl : (σ' y).val + 1 = (σ y).val
          · exact (hnot ⟨x, y, hadj, Or.inr ⟨hxl, hyl⟩, hagree⟩).elim
          · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
      · exact spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1 hxy lam hne hxr hxl
  · exact spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy lam hagree

/-- A bond entry on an adjacent pair vanishes unless the pair is either a
transverse `RaiseLowerStepS` or a `ParityBondStepS`. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_not_raiseLowerStepS_not_parityBondStepS
    {G : SimpleGraph Λ} {x y : Λ} (hadj : G.Adj x y) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hnot_raiseLower : ¬ RaiseLowerStepS G σ σ')
    (hnot_parityBond : ¬ ParityBondStepS G σ σ') :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hxy : x ≠ y := hadj.ne
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · by_cases hxr : (σ x).val + 1 = (σ' x).val
    · by_cases hyr : (σ y).val + 1 = (σ' y).val
      · exact (hnot_parityBond ⟨x, y, hadj, Or.inl ⟨hxr, hyr⟩, hagree⟩).elim
      · by_cases hyl : (σ' y).val + 1 = (σ y).val
        · exact (hnot_raiseLower ⟨x, y, hadj, Or.inl ⟨hxr, hyl⟩, hagree⟩).elim
        · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
    · by_cases hxl : (σ' x).val + 1 = (σ x).val
      · by_cases hyr : (σ y).val + 1 = (σ' y).val
        · exact (hnot_raiseLower ⟨x, y, hadj, Or.inr ⟨hxl, hyr⟩, hagree⟩).elim
        · by_cases hyl : (σ' y).val + 1 = (σ y).val
          · exact (hnot_parityBond ⟨x, y, hadj, Or.inr ⟨hxl, hyl⟩, hagree⟩).elim
          · exact spinSDotXXZSwap_apply_eq_zero_of_y_not_pm1 hxy lam hne hyr hyl
      · exact spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1 hxy lam hne hxr hxl
  · exact spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy lam hagree

/-! ## Total-entry zero tests -/

/-- On an equal-`magSumS` off-diagonal pair, the dressed real entry vanishes
unless the pair is a transverse `RaiseLowerStepS`. -/
theorem dressedAxisSwappedReMatrix_zero_of_magSum_eq_not_raiseLowerStepS
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' = magSumS σ)
    (hnot : ¬ RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ') :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  have hbonds_zero :
      ((∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N)
        σ' σ) = 0 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hadj : (bipartiteCompleteGraphOf A).Adj x y
    · rw [spinSDotXXZSwap_apply_eq_zero_of_magSum_eq_not_raiseLowerStepS
        hadj lam hne hmag hnot, mul_zero]
    · rw [hJsupp x y hadj, zero_mul]
  have hnot_single : ¬ SingleIonStepS σ σ' := by
    intro hstep
    have hstep_mag := singleIonStepS_magSumS_add_two_or_add_two_magSumS hstep
    omega
  have hsingle_zero : singleIonAnisotropyS2 D N σ' σ = 0 :=
    singleIonAnisotropyS2_apply_eq_zero_of_not_singleIonStepS D N hne hnot_single
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_apply,
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hbonds_zero,
    hsingle_zero, zero_add, mul_zero, Complex.zero_re]

/-- On a target-raised-by-two off-diagonal pair, the dressed real entry
vanishes unless the pair is a `ParityBondStepS` or `SingleIonStepS`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_magSum_add_two_not_step
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' = magSumS σ + 2)
    (hnot_bond : ¬ ParityBondStepS (bipartiteCompleteGraphOf A) σ σ')
    (hnot_single : ¬ SingleIonStepS σ σ') :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  have hbonds_zero :
      ((∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N)
        σ' σ) = 0 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hadj : (bipartiteCompleteGraphOf A).Adj x y
    · rw [spinSDotXXZSwap_apply_eq_zero_of_magSum_add_two_not_parityBondStepS
        hadj lam hne hmag hnot_bond, mul_zero]
    · rw [hJsupp x y hadj, zero_mul]
  have hsingle_zero : singleIonAnisotropyS2 D N σ' σ = 0 :=
    singleIonAnisotropyS2_apply_eq_zero_of_not_singleIonStepS D N hne hnot_single
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_apply,
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hbonds_zero,
    hsingle_zero, zero_add, mul_zero, Complex.zero_re]

/-- On a source-raised-by-two off-diagonal pair, the dressed real entry
vanishes unless the pair is a `ParityBondStepS` or `SingleIonStepS`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_add_two_magSum_not_step
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' + 2 = magSumS σ)
    (hnot_bond : ¬ ParityBondStepS (bipartiteCompleteGraphOf A) σ σ')
    (hnot_single : ¬ SingleIonStepS σ σ') :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  have hbonds_zero :
      ((∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N)
        σ' σ) = 0 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hadj : (bipartiteCompleteGraphOf A).Adj x y
    · rw [spinSDotXXZSwap_apply_eq_zero_of_add_two_magSum_not_parityBondStepS
        hadj lam hne hmag hnot_bond, mul_zero]
    · rw [hJsupp x y hadj, zero_mul]
  have hsingle_zero : singleIonAnisotropyS2 D N σ' σ = 0 :=
    singleIonAnisotropyS2_apply_eq_zero_of_not_singleIonStepS D N hne hnot_single
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_apply,
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hbonds_zero,
    hsingle_zero, zero_add, mul_zero, Complex.zero_re]

/-- If no local raw step is present, the dressed real entry vanishes. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_not_local_step
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hnot_raiseLower : ¬ RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ')
    (hnot_parityBond : ¬ ParityBondStepS (bipartiteCompleteGraphOf A) σ σ')
    (hnot_single : ¬ SingleIonStepS σ σ') :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  have hbonds_zero :
      ((∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N)
        σ' σ) = 0 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hadj : (bipartiteCompleteGraphOf A).Adj x y
    · rw [spinSDotXXZSwap_apply_eq_zero_of_not_raiseLowerStepS_not_parityBondStepS
        hadj lam hne hnot_raiseLower hnot_parityBond, mul_zero]
    · rw [hJsupp x y hadj, zero_mul]
  have hsingle_zero : singleIonAnisotropyS2 D N σ' σ = 0 :=
    singleIonAnisotropyS2_apply_eq_zero_of_not_singleIonStepS D N hne hnot_single
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_apply,
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hbonds_zero,
    hsingle_zero, zero_add, mul_zero, Complex.zero_re]

/-! ## Step-or-zero support split from raw entries -/

/-- Equal-`magSumS` raw support split: either a transverse step is present or
the dressed real entry is zero. -/
theorem dressedAxisSwappedReMatrix_raiseLower_or_zero_of_magSum_eq
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' = magSumS σ) :
    RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ' ∨
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  by_cases hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ'
  · exact Or.inl hstep
  · exact Or.inr <|
      dressedAxisSwappedReMatrix_zero_of_magSum_eq_not_raiseLowerStepS
        A hJsupp hne hmag hstep

/-- Target-raised-by-two raw support split: either a parity-bond step, a
single-ion step, or zero support is present. -/
theorem dressedAxisSwappedReMatrix_parity_or_single_or_zero_of_magSum_add_two
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' = magSumS σ + 2) :
    ParityBondStepS (bipartiteCompleteGraphOf A) σ σ' ∨
      SingleIonStepS σ σ' ∨
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  by_cases hbond : ParityBondStepS (bipartiteCompleteGraphOf A) σ σ'
  · exact Or.inl hbond
  · by_cases hsingle : SingleIonStepS σ σ'
    · exact Or.inr (Or.inl hsingle)
    · exact Or.inr (Or.inr <|
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_magSum_add_two_not_step
          A hJsupp hne hmag hbond hsingle)

/-- Source-raised-by-two raw support split: either a parity-bond step, a
single-ion step, or zero support is present. -/
theorem dressedAxisSwappedReMatrix_parity_or_single_or_zero_of_add_two_magSum
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag : magSumS σ' + 2 = magSumS σ) :
    ParityBondStepS (bipartiteCompleteGraphOf A) σ σ' ∨
      SingleIonStepS σ σ' ∨
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  by_cases hbond : ParityBondStepS (bipartiteCompleteGraphOf A) σ σ'
  · exact Or.inl hbond
  · by_cases hsingle : SingleIonStepS σ σ'
    · exact Or.inr (Or.inl hsingle)
    · exact Or.inr (Or.inr <|
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_add_two_magSum_not_step
          A hJsupp hne hmag hbond hsingle)

/-- Other `magSumS` changes have zero raw support. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_not_magSum_step
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam D : ℂ}
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hmag_eq : magSumS σ' ≠ magSumS σ)
    (hmag_up : magSumS σ' ≠ magSumS σ + 2)
    (hmag_down : magSumS σ' + 2 ≠ magSumS σ) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ' σ = 0 := by
  by_cases hrl : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ'
  · exact (hmag_eq (magSumS_eq_of_raiseLowerStepS hrl)).elim
  · by_cases hbond : ParityBondStepS (bipartiteCompleteGraphOf A) σ σ'
    · have hbond_mag := parityBondStepS_magSumS_add_two_or_add_two_magSumS hbond
      rcases hbond_mag with h | h
      · exact (hmag_up h).elim
      · exact (hmag_down h).elim
    · by_cases hsingle : SingleIonStepS σ σ'
      · have hsingle_mag := singleIonStepS_magSumS_add_two_or_add_two_magSumS hsingle
        rcases hsingle_mag with h | h
        · exact (hmag_up h).elim
        · exact (hmag_down h).elim
      · exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_not_local_step
          A hJsupp hne hrl hbond hsingle

/-! ## Block-level raw-support wrappers -/

/-- Entrywise non-negativity of the shifted case-II parity-gauged block from
raw total-Hamiltonian support classification. -/
theorem shiftedCaseIIParityGaugedBlock_nonneg_of_raw_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ)
    (hc : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c)
    (σ τ : parityConfigS Λ N p) :
    0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ := by
  refine shiftedCaseIIParityGaugedBlock_nonneg_of_step_support
    A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg p hc ?_ ?_ ?_ ?_ σ τ
  · intro σ τ hne hmag
    have hne_val : τ.1 ≠ σ.1 := fun h => hne (Subtype.ext h)
    exact dressedAxisSwappedReMatrix_raiseLower_or_zero_of_magSum_eq
      A hJsupp hne_val hmag
  · intro σ τ hne hmag
    have hne_val : τ.1 ≠ σ.1 := fun h => hne (Subtype.ext h)
    exact
      dressedAxisSwappedReMatrix_parity_or_single_or_zero_of_magSum_add_two
        A hJsupp hne_val hmag
  · intro σ τ hne hmag
    have hne_val : τ.1 ≠ σ.1 := fun h => hne (Subtype.ext h)
    exact
      dressedAxisSwappedReMatrix_parity_or_single_or_zero_of_add_two_magSum
        A hJsupp hne_val hmag
  · intro σ τ hne hmag_eq hmag_up hmag_down
    have hne_val : τ.1 ≠ σ.1 := fun h => hne (Subtype.ext h)
    exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_eq_zero_of_not_magSum_step
      A hJsupp hne_val hmag_eq hmag_up hmag_down

/-- Conditional irreducibility of the shifted case-II parity-gauged block from
raw total-Hamiltonian support classification and block reachability totality. -/
theorem shiftedCaseIIParityGaugedBlock_irreducible_of_raw_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ)
    (hc_strict : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  have hc_le : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c :=
    fun σ => le_of_lt (hc_strict σ)
  have hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ :=
    shiftedCaseIIParityGaugedBlock_nonneg_of_raw_support
      A hJim hJnn hJpos hJself hJsupp hlam hlb hlam_gt hDim hDneg p hc_le
  exact shiftedCaseIIParityGaugedBlock_isIrreducible_of_blockReachable_total
    A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg p hc_strict hB_nn hreach_total

end LatticeSystem.Quantum
