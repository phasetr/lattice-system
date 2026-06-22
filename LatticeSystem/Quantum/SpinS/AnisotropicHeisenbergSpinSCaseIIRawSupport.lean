import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIRawSupportCore

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
