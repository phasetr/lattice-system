import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockNonneg

/-!
# Case (ii): step-support bridge for the parity-gauged block matrix

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file bridges the case-(ii) local sign layer to the `magSumS` support split
used by the block non-negativity theorem.  The remaining support-classification
work is to prove the step-or-zero hypotheses from the raw total Hamiltonian
matrix entry.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Step-level dressed signs -/

/-- In case (ii), a transverse `RaiseLowerStepS` gives a non-positive dressed
real matrix entry. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonpos_of_raiseLowerStepS_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {D : ℂ}
    {σ τ : Λ → Fin (N + 1)}
    (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ τ) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ σ ≤ 0 :=
  le_of_lt <| dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_caseII
    A hJim hJnn hJpos hJself hlam hlb hstep

/-- In case (ii), a parity-bond `ParityBondStepS` gives a non-negative dressed
real matrix entry. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonneg_of_parityBondStepS_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlam_gt : 1 < lam.re)
    {D : ℂ}
    {σ τ : Λ → Fin (N + 1)}
    (hstep : ParityBondStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ σ :=
  le_of_lt <| dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_pos_of_parityBondStepS_caseII
    A hJim hJnn hJpos hJself hlam hlam_gt hstep

/-- In case (ii), a single-ion `SingleIonStepS` gives a non-negative dressed
real matrix entry. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonneg_of_singleIonStepS_caseII
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ}
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {σ τ : Λ → Fin (N + 1)} (hstep : SingleIonStepS σ τ) :
    0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ σ :=
  le_of_lt <| dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_pos_of_singleIonStepS_caseII
    A hJself hDim hDneg hstep

/-! ## Block-level bridge from a step-or-zero support split -/

/-- A zero dressed real entry gives a zero case-(ii) parity-gauged block entry. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_zero_of_dressed_zero
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (p : ℕ)
    {σ τ : parityConfigS Λ N p}
    (hzero : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ = 0 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply, hzero]
  ring

/-- Entrywise non-negativity of the case-(ii) shifted parity-gauged block from a
step-or-zero support split. -/
theorem shiftedCaseIIParityGaugedBlock_nonneg_of_step_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ)
    (hc : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c)
    (heq_step : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 →
      RaiseLowerStepS (bipartiteCompleteGraphOf A) σ.1 τ.1 ∨
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (hup_step : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 + 2 →
      ParityBondStepS (bipartiteCompleteGraphOf A) σ.1 τ.1 ∨
        SingleIonStepS σ.1 τ.1 ∨
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (hdown_step : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 + 2 = magSumS σ.1 →
      ParityBondStepS (bipartiteCompleteGraphOf A) σ.1 τ.1 ∨
        SingleIonStepS σ.1 τ.1 ∨
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (hzero : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 ≠ magSumS σ.1 →
      magSumS τ.1 ≠ magSumS σ.1 + 2 →
      magSumS τ.1 + 2 ≠ magSumS σ.1 →
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (σ τ : parityConfigS Λ N p) :
    0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ := by
  refine shiftedCaseIIParityGaugedBlock_nonneg_of_magSum_support
    A J lam D N p hc ?_ ?_ ?_ ?_ σ τ
  · intro σ τ hne hmag
    rcases heq_step hne hmag with hstep | hzero_entry
    · exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonpos_of_raiseLowerStepS_caseII
        A hJim hJnn hJpos hJself hlam hlb hstep
    · rw [hzero_entry]
  · intro σ τ hne hmag
    rcases hup_step hne hmag with hPB | hSI | hzero_entry
    · exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonneg_of_parityBondStepS_caseII
        A hJim hJnn hJpos hJself hlam hlam_gt hPB
    · exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonneg_of_singleIonStepS_caseII
        A hJself hDim hDneg hSI
    · rw [hzero_entry]
  · intro σ τ hne hmag
    rcases hdown_step hne hmag with hPB | hSI | hzero_entry
    · exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonneg_of_parityBondStepS_caseII
        A hJim hJnn hJpos hJself hlam hlam_gt hPB
    · exact dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply_nonneg_of_singleIonStepS_caseII
        A hJself hDim hDneg hSI
    · rw [hzero_entry]
  · intro σ τ hne hmag_eq hmag_up hmag_down
    exact caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_zero_of_dressed_zero
      A J lam D N p (hzero hne hmag_eq hmag_up hmag_down)

/-- Conditional irreducibility of the case-(ii) shifted parity-gauged block from
a step-or-zero support split and block reachability totality. -/
theorem shiftedCaseIIParityGaugedBlock_irreducible_of_step_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ)
    (hc_strict : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c)
    (heq_step : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 →
      RaiseLowerStepS (bipartiteCompleteGraphOf A) σ.1 τ.1 ∨
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (hup_step : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 + 2 →
      ParityBondStepS (bipartiteCompleteGraphOf A) σ.1 τ.1 ∨
        SingleIonStepS σ.1 τ.1 ∨
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (hdown_step : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 + 2 = magSumS σ.1 →
      ParityBondStepS (bipartiteCompleteGraphOf A) σ.1 τ.1 ∨
        SingleIonStepS σ.1 τ.1 ∨
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    (hzero : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 ≠ magSumS σ.1 →
      magSumS τ.1 ≠ magSumS σ.1 + 2 →
      magSumS τ.1 + 2 ≠ magSumS σ.1 →
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 = 0)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  have hc_le : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c :=
    fun σ => le_of_lt (hc_strict σ)
  have hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ :=
    shiftedCaseIIParityGaugedBlock_nonneg_of_step_support
      A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg p hc_le
      heq_step hup_step hdown_step hzero
  exact shiftedCaseIIParityGaugedBlock_isIrreducible_of_blockReachable_total
    A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg p hc_strict hB_nn hreach_total

end LatticeSystem.Quantum
