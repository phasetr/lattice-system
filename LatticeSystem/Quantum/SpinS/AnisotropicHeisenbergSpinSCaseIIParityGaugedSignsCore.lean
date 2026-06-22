import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityGaugedMatrix

/-!
# Case (ii) parity-gauged signs: products and entry transfer (foundation)

Foundational layer extracted from `AnisotropicHeisenbergSpinSCaseIIParityGaugedSigns.lean` for build
speed.  This file proves the real parity-gauge products and the parity-gauged entry sign transfer
for the case-(ii) axis-swapped parity-block matrix.

The shifted-matrix sign transfer (`shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_*`) is
kept in the capstone module `AnisotropicHeisenbergSpinSCaseIIParityGaugedSigns.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Real parity-gauge products -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- Powers of `-1 : ℝ` square to one. -/
theorem neg_one_pow_mul_self_real (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
  rw [← pow_add]
  rw [Even.neg_one_pow (even_add_self_nat k)]

omit [Fintype Λ] [DecidableEq Λ] in
/-- A successive real `-1` power multiplied by the previous one gives `-1`. -/
theorem neg_one_pow_succ_mul_self_real (k : ℕ) :
    ((-1 : ℝ) ^ (k + 1)) * ((-1 : ℝ) ^ k) = -1 := by
  rw [pow_succ]
  have hs := neg_one_pow_mul_self_real k
  rw [mul_assoc, mul_comm (-1 : ℝ) ((-1 : ℝ) ^ k), ← mul_assoc, hs]
  norm_num

omit [Fintype Λ] [DecidableEq Λ] in
/-- The previous real `-1` power multiplied by a successive one gives `-1`. -/
theorem neg_one_pow_mul_succ_self_real (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k + 1)) = -1 := by
  rw [mul_comm]
  exact neg_one_pow_succ_mul_self_real k

omit [DecidableEq Λ] in
/-- The real case-(ii) parity gauge is unchanged across equal-`magSumS` pairs. -/
theorem caseIIParityGaugeSignReal_mul_eq_one_of_magSumS_eq {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1) :
    caseIIParityGaugeSignReal τ * caseIIParityGaugeSignReal σ = 1 := by
  unfold caseIIParityGaugeSignReal
  rw [hmag]
  exact neg_one_pow_mul_self_real (magSumS σ.1 / 2)

omit [DecidableEq Λ] in
/-- The real case-(ii) parity gauge flips sign when the target `magSumS` is raised by two. -/
theorem caseIIParityGaugeSignReal_mul_eq_neg_one_of_magSumS_add_two {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1 + 2) :
    caseIIParityGaugeSignReal τ * caseIIParityGaugeSignReal σ = -1 := by
  unfold caseIIParityGaugeSignReal
  rw [hmag]
  have hdiv : (magSumS σ.1 + 2) / 2 = magSumS σ.1 / 2 + 1 := by omega
  rw [hdiv]
  exact neg_one_pow_succ_mul_self_real (magSumS σ.1 / 2)

omit [DecidableEq Λ] in
/-- The real case-(ii) parity gauge flips sign when the source `magSumS` is raised by two. -/
theorem caseIIParityGaugeSignReal_mul_eq_neg_one_of_add_two_magSumS {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 + 2 = magSumS σ.1) :
    caseIIParityGaugeSignReal τ * caseIIParityGaugeSignReal σ = -1 := by
  unfold caseIIParityGaugeSignReal
  have hdiv : magSumS σ.1 / 2 = magSumS τ.1 / 2 + 1 := by omega
  rw [hdiv]
  exact neg_one_pow_mul_succ_self_real (magSumS τ.1 / 2)

/-! ## Parity-gauged entry sign transfer -/

/-- Across equal-`magSumS` pairs, the case-(ii) parity gauge leaves the dressed real entry
unchanged. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_of_magSumS_eq
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ =
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply]
  have hXi := caseIIParityGaugeSignReal_mul_eq_one_of_magSumS_eq hmag
  calc
    caseIIParityGaugeSignReal τ *
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 *
        caseIIParityGaugeSignReal σ
        = (caseIIParityGaugeSignReal τ * caseIIParityGaugeSignReal σ) *
            dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by ring
    _ = dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by
        rw [hXi, one_mul]

/-- If the target `magSumS` is raised by two, the case-(ii) parity gauge negates the dressed real
entry. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_magSumS_add_two
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1 + 2) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ =
      -dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply]
  have hXi := caseIIParityGaugeSignReal_mul_eq_neg_one_of_magSumS_add_two hmag
  calc
    caseIIParityGaugeSignReal τ *
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 *
        caseIIParityGaugeSignReal σ
        = (caseIIParityGaugeSignReal τ * caseIIParityGaugeSignReal σ) *
            dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by ring
    _ = -dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by
        rw [hXi]; ring

/-- If the source `magSumS` is raised by two, the case-(ii) parity gauge negates the dressed real
entry. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_add_two_magSumS
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 + 2 = magSumS σ.1) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ =
      -dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply]
  have hXi := caseIIParityGaugeSignReal_mul_eq_neg_one_of_add_two_magSumS hmag
  calc
    caseIIParityGaugeSignReal τ *
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 *
        caseIIParityGaugeSignReal σ
        = (caseIIParityGaugeSignReal τ * caseIIParityGaugeSignReal σ) *
            dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by ring
    _ = -dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 := by
        rw [hXi]; ring

/-- Equal-`magSumS` dressed negativity transfers to parity-gauged negativity. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_magSumS_eq
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1)
    (hentry : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 ≤ 0) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ ≤ 0 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_of_magSumS_eq A J lam D N hmag]
  exact hentry

/-- Target-raised-by-two dressed non-negativity transfers to parity-gauged non-positivity. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_magSumS_add_two
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1 + 2)
    (hentry : 0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ ≤ 0 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_magSumS_add_two A J lam D N hmag]
  linarith

/-- Source-raised-by-two dressed non-negativity transfers to parity-gauged non-positivity. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonpos_of_add_two_magSumS
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 + 2 = magSumS σ.1)
    (hentry : 0 ≤ dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ ≤ 0 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_add_two_magSumS A J lam D N hmag]
  linarith

end LatticeSystem.Quantum
