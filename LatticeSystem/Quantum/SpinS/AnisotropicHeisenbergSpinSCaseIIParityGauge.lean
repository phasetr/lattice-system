import LatticeSystem.Quantum.SpinS.ParityConfig

/-!
# Case (ii): parity-block gauge signs

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

In case (ii), `lambda >= 1` and `D <= 0`, the Marshall sign alone does not
put every parity-block off-diagonal entry into the case-(i) Perron--Frobenius
sign convention.  The parity-bond and single-ion moves change `magSumS` by
`±2`, while transverse raise-lower moves preserve `magSumS`.  The additional
parity-block gauge `(-1)^(magSumS / 2)` therefore flips exactly the `±2`
moves and preserves the magnetization-preserving moves.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Scalar gauge sign -/

/-- The case-(ii) extra parity-block gauge sign `(-1)^(magSumS / 2)`.

On each fixed parity block this is equivalent to Tasaki's block-wise
`(-1)^((magSumS - p) / 2)` convention up to a constant block sign; it preserves
`magSumS`-preserving moves and flips `±2` moves. -/
def caseIIParityGaugeSign {p : ℕ} (σ : parityConfigS Λ N p) : ℂ :=
  (-1 : ℂ) ^ (magSumS σ.1 / 2)

omit [Fintype Λ] [DecidableEq Λ] in
/-- The sum `k + k` is even. -/
theorem even_add_self_nat (k : ℕ) : Even (k + k) :=
  ⟨k, by omega⟩

omit [Fintype Λ] [DecidableEq Λ] in
/-- Powers of `-1` square to one. -/
theorem neg_one_pow_mul_self_complex (k : ℕ) :
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← pow_add]
  rw [Even.neg_one_pow (even_add_self_nat k)]

omit [Fintype Λ] [DecidableEq Λ] in
/-- A successive `-1` power multiplied by the previous one gives `-1`. -/
theorem neg_one_pow_succ_mul_self_complex (k : ℕ) :
    ((-1 : ℂ) ^ (k + 1)) * ((-1 : ℂ) ^ k) = -1 := by
  rw [pow_succ]
  have hs := neg_one_pow_mul_self_complex k
  rw [mul_assoc, mul_comm (-1 : ℂ) ((-1 : ℂ) ^ k), ← mul_assoc, hs]
  norm_num

omit [Fintype Λ] [DecidableEq Λ] in
/-- The previous `-1` power multiplied by a successive one gives `-1`. -/
theorem neg_one_pow_mul_succ_self_complex (k : ℕ) :
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ (k + 1)) = -1 := by
  rw [mul_comm]
  exact neg_one_pow_succ_mul_self_complex k

omit [DecidableEq Λ] in
/-- The case-(ii) parity gauge sign squares to one. -/
theorem caseIIParityGaugeSign_mul_self {p : ℕ} (σ : parityConfigS Λ N p) :
    caseIIParityGaugeSign σ * caseIIParityGaugeSign σ = 1 := by
  unfold caseIIParityGaugeSign
  exact neg_one_pow_mul_self_complex (magSumS σ.1 / 2)

omit [DecidableEq Λ] in
/-- The case-(ii) parity gauge is unchanged across equal-`magSumS` pairs. -/
theorem caseIIParityGaugeSign_mul_eq_one_of_magSumS_eq {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1) :
    caseIIParityGaugeSign τ * caseIIParityGaugeSign σ = 1 := by
  unfold caseIIParityGaugeSign
  rw [hmag]
  exact neg_one_pow_mul_self_complex (magSumS σ.1 / 2)

omit [DecidableEq Λ] in
/-- The case-(ii) parity gauge flips sign when the target `magSumS` is raised by two. -/
theorem caseIIParityGaugeSign_mul_eq_neg_one_of_magSumS_add_two {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 = magSumS σ.1 + 2) :
    caseIIParityGaugeSign τ * caseIIParityGaugeSign σ = -1 := by
  unfold caseIIParityGaugeSign
  rw [hmag]
  have hdiv : (magSumS σ.1 + 2) / 2 = magSumS σ.1 / 2 + 1 := by omega
  rw [hdiv]
  exact neg_one_pow_succ_mul_self_complex (magSumS σ.1 / 2)

omit [DecidableEq Λ] in
/-- The case-(ii) parity gauge flips sign when the source `magSumS` is raised by two. -/
theorem caseIIParityGaugeSign_mul_eq_neg_one_of_add_two_magSumS {p : ℕ}
    {σ τ : parityConfigS Λ N p} (hmag : magSumS τ.1 + 2 = magSumS σ.1) :
    caseIIParityGaugeSign τ * caseIIParityGaugeSign σ = -1 := by
  unfold caseIIParityGaugeSign
  have hdiv : magSumS σ.1 / 2 = magSumS τ.1 / 2 + 1 := by omega
  rw [hdiv]
  exact neg_one_pow_mul_succ_self_complex (magSumS τ.1 / 2)

/-! ## Diagonal gauge on parity blocks -/

/-- The case-(ii) parity gauge diagonal on a fixed parity block. -/
noncomputable def caseIIParityGaugeDiagonalOnParity (p : ℕ) :
    Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℂ :=
  Matrix.diagonal (caseIIParityGaugeSign (Λ := Λ) (N := N))

/-- The case-(ii) parity gauge diagonal squares to the identity. -/
theorem caseIIParityGaugeDiagonalOnParity_mul_self (p : ℕ) :
    caseIIParityGaugeDiagonalOnParity (Λ := Λ) (N := N) p *
      caseIIParityGaugeDiagonalOnParity (Λ := Λ) (N := N) p = 1 := by
  unfold caseIIParityGaugeDiagonalOnParity
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : parityConfigS Λ N p =>
        caseIIParityGaugeSign σ * caseIIParityGaugeSign σ) = (fun _ => (1 : ℂ)) from
      funext fun σ => caseIIParityGaugeSign_mul_self σ]
  exact Matrix.diagonal_one

end LatticeSystem.Quantum
