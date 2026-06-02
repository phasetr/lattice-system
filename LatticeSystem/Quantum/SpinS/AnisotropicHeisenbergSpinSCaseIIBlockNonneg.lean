import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockIrreducible

/-!
# Case (ii): parity-gauged shifted block non-negativity

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file packages the remaining sign-transfer bridge between local/support
information and entrywise non-negativity of the case-(ii) parity-gauged shifted
block matrix.

The main input is a `magSumS` support split for off-diagonal block entries:
equal `magSumS` entries are dressed-non-positive, `±2` entries are
dressed-non-negative, and all other off-diagonal entries have zero
parity-gauged support.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Off-diagonal non-positivity from support split -/

/-- The case-(ii) parity-gauged real block matrix has non-positive off-diagonal
entries once the off-diagonal support is split by the three possible
`magSumS` changes. -/
theorem caseIIParityGaugedBlock_offdiag_nonpos_of_magSum_support
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    (heq : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 →
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 ≤ 0)
    (hup : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 + 2 →
      0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1)
    (hdown : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 + 2 = magSumS σ.1 →
      0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1)
    (hzero : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 ≠ magSumS σ.1 →
      magSumS τ.1 ≠ magSumS σ.1 + 2 →
      magSumS τ.1 + 2 ≠ magSumS σ.1 →
      caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ = 0)
    {σ τ : parityConfigS Λ N p} (hne : τ ≠ σ) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ ≤ 0 := by
  by_cases hmag_eq : magSumS τ.1 = magSumS σ.1
  · exact caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_magSumS_eq
      A J lam D N hmag_eq (heq hne hmag_eq)
  · by_cases hmag_up : magSumS τ.1 = magSumS σ.1 + 2
    · exact caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_magSumS_add_two
        A J lam D N hmag_up (hup hne hmag_up)
    · by_cases hmag_down : magSumS τ.1 + 2 = magSumS σ.1
      · exact caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_add_two_magSumS
          A J lam D N hmag_down (hdown hne hmag_down)
      · rw [hzero hne hmag_eq hmag_up hmag_down]

/-! ## Shifted entrywise non-negativity -/

/-- Entrywise non-negativity of the case-(ii) shifted parity-gauged block matrix
from a diagonal shift bound and the `magSumS` off-diagonal support split. -/
theorem shiftedCaseIIParityGaugedBlock_nonneg_of_magSum_support
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ} (p : ℕ)
    (hc : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c)
    (heq : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 →
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 ≤ 0)
    (hup : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 + 2 →
      0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1)
    (hdown : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 + 2 = magSumS σ.1 →
      0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1)
    (hzero : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 ≠ magSumS σ.1 →
      magSumS τ.1 ≠ magSumS σ.1 + 2 →
      magSumS τ.1 + 2 ≠ magSumS σ.1 →
      caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ = 0)
    (σ τ : parityConfigS Λ N p) :
    0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ := by
  refine shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonneg
    A J lam D N p hc ?_ σ τ
  intro σ τ hne
  exact caseIIParityGaugedBlock_offdiag_nonpos_of_magSum_support
    A J lam D N heq hup hdown hzero hne

/-! ## Conditional irreducibility with explicit non-negativity bridge -/

/-- The case-(ii) shifted parity-gauged block matrix is irreducible from the
`magSumS` support split, strict diagonal shift, and block-reachability
totality. -/
theorem shiftedCaseIIParityGaugedBlock_irreducible_of_magSum_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ)
    (hc_strict : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c)
    (heq : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 →
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 ≤ 0)
    (hup : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 = magSumS σ.1 + 2 →
      0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1)
    (hdown : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 + 2 = magSumS σ.1 →
      0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1)
    (hzero : ∀ {σ τ : parityConfigS Λ N p}, τ ≠ σ →
      magSumS τ.1 ≠ magSumS σ.1 →
      magSumS τ.1 ≠ magSumS σ.1 + 2 →
      magSumS τ.1 + 2 ≠ magSumS σ.1 →
      caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ = 0)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  have hc_le : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c :=
    fun σ => le_of_lt (hc_strict σ)
  have hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ :=
    shiftedCaseIIParityGaugedBlock_nonneg_of_magSum_support
      A J lam D N p hc_le heq hup hdown hzero
  exact shiftedCaseIIParityGaugedBlock_isIrreducible_of_blockReachable_total
    A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg p hc_strict hB_nn hreach_total

end LatticeSystem.Quantum
