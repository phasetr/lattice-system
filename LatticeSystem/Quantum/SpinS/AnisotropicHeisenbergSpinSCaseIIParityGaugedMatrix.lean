import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIParityGauge
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.MarshallSubmatrixMinEq

/-!
# Case (ii): parity-gauged shifted PF matrix layer

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

The case-(ii) parity gauge from
`AnisotropicHeisenbergSpinSCaseIIParityGauge` is combined here with the
Marshall-dressed axis-swapped real matrix.  The resulting block matrix is the
structural target for the `lambda >= 1`, `D <= 0` Perron--Frobenius route:
the later sign lemmas will show that its shifted version is non-negative and
irreducible on each parity block.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Real parity gauge and combined diagonal -/

/-- The real-valued case-(ii) extra parity-block gauge sign `(-1)^(magSumS / 2)`. -/
def caseIIParityGaugeSignReal {p : ℕ} (σ : parityConfigS Λ N p) : ℝ :=
  (-1 : ℝ) ^ (magSumS σ.1 / 2)

omit [DecidableEq Λ] in
/-- The real case-(ii) parity gauge sign squares to one. -/
theorem caseIIParityGaugeSignReal_mul_self {p : ℕ} (σ : parityConfigS Λ N p) :
    caseIIParityGaugeSignReal σ * caseIIParityGaugeSignReal σ = 1 := by
  unfold caseIIParityGaugeSignReal
  rw [← pow_add]
  rw [Even.neg_one_pow (even_add_self_nat (magSumS σ.1 / 2))]

omit [DecidableEq Λ] in
/-- The real combined case-(ii) gauge sign on a parity block. -/
noncomputable def caseIICombinedGaugeSignOnParity (A : Λ → Bool) {p : ℕ}
    (σ : parityConfigS Λ N p) : ℝ :=
  caseIIParityGaugeSignReal σ * (marshallSignS A σ.1).re

omit [DecidableEq Λ] in
/-- The real combined case-(ii) gauge sign squares to one. -/
theorem caseIICombinedGaugeSignOnParity_mul_self (A : Λ → Bool) {p : ℕ}
    (σ : parityConfigS Λ N p) :
    caseIICombinedGaugeSignOnParity A σ * caseIICombinedGaugeSignOnParity A σ = 1 := by
  unfold caseIICombinedGaugeSignOnParity
  have hXi := caseIIParityGaugeSignReal_mul_self σ
  have hM := marshallSignS_re_sq A σ.1
  calc
    (caseIIParityGaugeSignReal σ * (marshallSignS A σ.1).re) *
        (caseIIParityGaugeSignReal σ * (marshallSignS A σ.1).re)
        = (caseIIParityGaugeSignReal σ * caseIIParityGaugeSignReal σ) *
            ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) := by ring
    _ = 1 := by rw [hXi, hM, one_mul]

/-- The real combined case-(ii) gauge diagonal on a fixed parity block. -/
noncomputable def caseIICombinedGaugeDiagonalOnParity (A : Λ → Bool) (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
  Matrix.diagonal (caseIICombinedGaugeSignOnParity (Λ := Λ) (N := N) A)

/-- The real combined case-(ii) gauge diagonal squares to the identity. -/
theorem caseIICombinedGaugeDiagonalOnParity_mul_self (A : Λ → Bool) (p : ℕ) :
    caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p *
      caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p = 1 := by
  unfold caseIICombinedGaugeDiagonalOnParity
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : parityConfigS Λ N p =>
        caseIICombinedGaugeSignOnParity A σ * caseIICombinedGaugeSignOnParity A σ) =
      (fun _ => (1 : ℝ)) from
        funext fun σ => caseIICombinedGaugeSignOnParity_mul_self A σ]
  exact Matrix.diagonal_one

/-! ## Parity-gauged real matrix on parity blocks -/

/-- The case-(ii) parity-gauged real matrix on a fixed axis-swapped parity block.

The Marshall dressing is already present in
`dressedAxisSwappedAnisotropicHeisenbergSReMatrix`; this definition applies the
additional case-(ii) parity gauge on the left and right. -/
noncomputable def caseIIParityGaugedAxisSwappedReMatrixOnParityBlock
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
  fun σ τ =>
    caseIIParityGaugeSignReal σ *
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 τ.1 *
      caseIIParityGaugeSignReal τ

/-- Component-wise unfolding of the case-(ii) parity-gauged real matrix. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (p : ℕ)
    (σ τ : parityConfigS Λ N p) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p σ τ =
      caseIIParityGaugeSignReal σ *
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 τ.1 *
        caseIIParityGaugeSignReal τ := rfl

/-- The parity-gauged real matrix has the same diagonal as the dressed real matrix. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (p : ℕ)
    (σ : parityConfigS Λ N p) :
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p σ σ =
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 := by
  rw [caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply]
  have hXi := caseIIParityGaugeSignReal_mul_self σ
  calc
    caseIIParityGaugeSignReal σ *
        dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 *
        caseIIParityGaugeSignReal σ
        = (caseIIParityGaugeSignReal σ * caseIIParityGaugeSignReal σ) *
            dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 := by ring
    _ = dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 := by
        rw [hXi, one_mul]

/-- The parity-gauged real matrix is symmetric for real coupling data. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0) (p : ℕ) :
    (caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p).IsSymm := by
  have hS := dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real
    (N := N) A hJ hlam hD
  ext σ τ
  rw [Matrix.transpose_apply,
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply,
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply]
  have h := congrFun (congrFun hS σ.1) τ.1
  rw [Matrix.transpose_apply] at h
  rw [h]
  ring

/-! ## Shifted parity-gauged matrix -/

/-- The shifted case-(ii) parity-gauged real matrix `c • 1 - R`. -/
noncomputable def shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
  c • 1 - caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p

/-- Component-wise unfolding of the shifted case-(ii) parity-gauged real matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (p : ℕ)
    (σ τ : parityConfigS Λ N p) :
    shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ =
      (c • 1 -
        caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p) σ τ := rfl

/-- Off-diagonal entry of the shifted case-(ii) parity-gauged matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_off_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (p : ℕ)
    {σ τ : parityConfigS Λ N p} (hne : σ ≠ τ) :
    shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ =
      -caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p σ τ := by
  unfold shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock
  simp [Matrix.sub_apply, Matrix.smul_apply, hne]

/-- Diagonal entry of the shifted case-(ii) parity-gauged matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) (c : ℝ) (p : ℕ)
    (σ : parityConfigS Λ N p) :
    shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ σ =
      c - caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p σ σ := by
  unfold shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock
  simp [Matrix.sub_apply, Matrix.smul_apply]

/-- Strict diagonal positivity for a strict shift. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_diag_pos
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) {c : ℝ} (p : ℕ)
    {σ : parityConfigS Λ N p}
    (hc : dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ σ := by
  rw [shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_diag,
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply_diag]
  linarith

/-- The shifted case-(ii) parity-gauged real matrix is symmetric for real coupling data. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (c : ℝ) (p : ℕ) :
    (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsSymm := by
  unfold shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock
  exact (Matrix.isSymm_one.smul c).sub
    (caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_isSymm_of_real A hJ hlam hD p)

end LatticeSystem.Quantum
