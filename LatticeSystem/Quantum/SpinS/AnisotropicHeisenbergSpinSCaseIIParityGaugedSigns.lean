import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityGaugedMatrix

/-!
# Case (ii): parity-gauged shifted PF sign-transfer layer

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file records the structural sign-transfer facts for the case-(ii)
parity-gauged real matrix.  The local `lambda >= 1`, `D <= 0` sign proofs can
now target the ungauged Marshall-dressed real entry: the extra parity gauge is
`+1` on equal-`magSumS` transverse moves and `-1` on `±2` parity-bond or
single-ion moves.  The shifted matrix then becomes entrywise non-negative once
the parity-gauged off-diagonal entries are non-positive.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
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

/-! ## Shifted matrix sign transfer -/

/-- Entrywise non-negativity of the shifted case-(ii) parity-gauged matrix from a diagonal shift
bound and off-diagonal non-positivity of the parity-gauged real matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_nonneg
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ} (p : ℕ)
    (hc : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c)
    (hoff : ∀ {σ τ : parityConfigS Λ N p}, σ ≠ τ →
      caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p σ τ ≤ 0)
    (σ τ : parityConfigS Λ N p) :
    0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ := by
  by_cases hdiag : σ = τ
  · subst hdiag
    rw [shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_diag,
      caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_diag]
    linarith [hc σ]
  · rw [shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_off_diag
      A J lam D N c p hdiag]
    linarith [hoff hdiag]

/-- A negative off-diagonal parity-gauged entry gives a strictly positive shifted entry. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_gauged_entry_neg
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hne : τ ≠ σ)
    (hentry : caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p τ σ < 0) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  rw [shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_off_diag
    A J lam D N c p hne]
  linarith

/-- Equal-`magSumS` dressed negativity gives strict positivity of the shifted case-(ii) entry. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_eq
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hne : τ ≠ σ) (hmag : magSumS τ.1 = magSumS σ.1)
    (hentry : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1 < 0) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  refine shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_gauged_entry_neg
    A J lam D N c hne ?_
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_of_magSumS_eq A J lam D N hmag]
  exact hentry

/-- Target-raised-by-two dressed positivity gives strict positivity of the shifted case-(ii)
entry. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_magSumS_add_two
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hne : τ ≠ σ) (hmag : magSumS τ.1 = magSumS σ.1 + 2)
    (hentry : 0 < dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  refine shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_gauged_entry_neg
    A J lam D N c hne ?_
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_magSumS_add_two
    A J lam D N hmag]
  linarith

/-- Source-raised-by-two dressed positivity gives strict positivity of the shifted case-(ii)
entry. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_add_two_magSumS
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hne : τ ≠ σ) (hmag : magSumS τ.1 + 2 = magSumS σ.1)
    (hentry : 0 < dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N τ.1 σ.1) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  refine shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_gauged_entry_neg
    A J lam D N c hne ?_
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_eq_neg_of_add_two_magSumS A J lam D N hmag]
  linarith

end LatticeSystem.Quantum
