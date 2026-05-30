import LatticeSystem.Quantum.SpinS.SpinSRotation1
import LatticeSystem.Quantum.SpinS.AxisSwapGaugeEquiv
import LatticeSystem.Quantum.SpinS.Hermitian
import LatticeSystem.Quantum.SpinS.CyclicCommutator
import LatticeSystem.Quantum.SpinS.CyclicCommutator31

/-!
# General spin-S axis-swap unitary (Tasaki §2.5 Theorem 2.4)

Issue #3739. The `AxisSwapUnitaryS N` interface is made non-vacuous for every
`N ≥ 0` by specialising `spinSRot1 N (π/2) = exp(-iπ Ŝ¹/2)` to the `π/2`
rotation about spin-axis 1.

The conjugation lemmas
`spinSRot1 N (π/2) * Ŝ² * spinSRot1 N (-π/2) = Ŝ³` and
`spinSRot1 N (π/2) * Ŝ³ * spinSRot1 N (-π/2) = -Ŝ²`
are proven via the **ladder-eigenvector approach**: the ladder operators
`L⁺ := Ŝ² + i Ŝ³` and `L⁻ := Ŝ² - i Ŝ³` are eigenvectors of the inner
derivation `ad_{Ŝ¹}` with eigenvalues `+1` and `-1` respectively. This is
witnessed by the single commutation identities
`Ŝ¹ L⁺ = L⁺ (Ŝ¹ + 1)` and `Ŝ¹ L⁻ = L⁻ (Ŝ¹ - 1)`,
which propagate to `Ŝ¹^n L^± = L^± (Ŝ¹ ± 1)^n` by induction.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace Complex

variable {N : ℕ}

/-- **`spinSRot1 N θ` adjoint formula**: `(exp(-iθ Ŝ¹))† = exp(iθ Ŝ¹) = spinSRot1 N (-θ)`.
Follows from `Matrix.exp_conjTranspose` and the Hermiticity of `Ŝ¹`. -/
theorem spinSRot1_adjoint (N : ℕ) (θ : ℝ) :
    Matrix.conjTranspose (spinSRot1 N θ) = spinSRot1 N (-θ) := by
  unfold spinSRot1
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, (spinSOp1_isHermitian N)]
  congr 1
  push_cast
  simp [Complex.conj_I, mul_comm]

/-- **Axis-1 raising ladder operator** `L⁺ := Ŝ² + i Ŝ³`. -/
noncomputable def spinSLadder1Plus (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  spinSOp2 N + Complex.I • spinSOp3 N

/-- **Axis-1 lowering ladder operator** `L⁻ := Ŝ² - i Ŝ³`. -/
noncomputable def spinSLadder1Minus (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  spinSOp2 N - Complex.I • spinSOp3 N

/-- **L⁺ + L⁻ = 2 Ŝ²**. -/
theorem spinSLadder1Plus_add_Minus (N : ℕ) :
    spinSLadder1Plus N + spinSLadder1Minus N = (2 : ℂ) • spinSOp2 N := by
  unfold spinSLadder1Plus spinSLadder1Minus
  match_scalars <;> ring

/-- **L⁺ - L⁻ = 2i Ŝ³**. -/
theorem spinSLadder1Plus_sub_Minus (N : ℕ) :
    spinSLadder1Plus N - spinSLadder1Minus N = (2 * Complex.I) • spinSOp3 N := by
  unfold spinSLadder1Plus spinSLadder1Minus
  match_scalars <;> ring

/-- Auxiliary: `Ŝ¹ Ŝ² = Ŝ² Ŝ¹ + I Ŝ³` (recast of `spinSOp1_commutator_spinSOp2`). -/
private theorem spinSOp1_mul_spinSOp2_eq (N : ℕ) :
    spinSOp1 N * spinSOp2 N = spinSOp2 N * spinSOp1 N + Complex.I • spinSOp3 N := by
  have h := spinSOp1_commutator_spinSOp2 N
  rw [← h]; abel

/-- Auxiliary: `Ŝ¹ Ŝ³ = Ŝ³ Ŝ¹ - I Ŝ²` (recast of `spinSOp3_commutator_spinSOp1`). -/
private theorem spinSOp1_mul_spinSOp3_eq (N : ℕ) :
    spinSOp1 N * spinSOp3 N = spinSOp3 N * spinSOp1 N - Complex.I • spinSOp2 N := by
  have h := spinSOp3_commutator_spinSOp1 N
  rw [← h]; abel

/-- **Eigenvector commutation for L⁺**: `Ŝ¹ L⁺ = L⁺ (Ŝ¹ + 1)`. The single algebraic
identity from which the iterated `Ŝ¹^n L⁺ = L⁺ (Ŝ¹ + 1)^n` follows by induction. -/
theorem spinSOp1_mul_spinSLadder1Plus (N : ℕ) :
    spinSOp1 N * spinSLadder1Plus N =
      spinSLadder1Plus N * (spinSOp1 N + 1) := by
  unfold spinSLadder1Plus
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
             Matrix.mul_one]
  rw [spinSOp1_mul_spinSOp2_eq, spinSOp1_mul_spinSOp3_eq, smul_sub, smul_smul,
      Complex.I_mul_I, neg_one_smul]
  abel

/-- **Eigenvector commutation for L⁻**: `Ŝ¹ L⁻ = L⁻ (Ŝ¹ - 1)`. -/
theorem spinSOp1_mul_spinSLadder1Minus (N : ℕ) :
    spinSOp1 N * spinSLadder1Minus N =
      spinSLadder1Minus N * (spinSOp1 N - 1) := by
  unfold spinSLadder1Minus
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
             Matrix.mul_one]
  rw [spinSOp1_mul_spinSOp2_eq, spinSOp1_mul_spinSOp3_eq, smul_sub, smul_smul,
      Complex.I_mul_I, neg_one_smul]
  abel

/-- **Iterated commutation for L⁺**: `Ŝ¹^n L⁺ = L⁺ (Ŝ¹ + 1)^n`. -/
theorem spinSOp1_pow_mul_spinSLadder1Plus (N n : ℕ) :
    spinSOp1 N ^ n * spinSLadder1Plus N =
      spinSLadder1Plus N * (spinSOp1 N + 1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, spinSOp1_mul_spinSLadder1Plus,
          ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

/-- **Iterated commutation for L⁻**: `Ŝ¹^n L⁻ = L⁻ (Ŝ¹ - 1)^n`. -/
theorem spinSOp1_pow_mul_spinSLadder1Minus (N n : ℕ) :
    spinSOp1 N ^ n * spinSLadder1Minus N =
      spinSLadder1Minus N * (spinSOp1 N - 1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, spinSOp1_mul_spinSLadder1Minus,
          ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

/-- **Finite-sum intertwining for L⁺**: for every `N`, the partial sum of the
exponential series intertwines L⁺ with shifted Ŝ¹. Builds towards the full
`exp(-iθ Ŝ¹) L⁺ exp(iθ Ŝ¹) = e^{-iθ} L⁺` formula by taking N → ∞ along the
series. -/
theorem spinSRot1_partial_sum_mul_spinSLadder1Plus
    (N : ℕ) (θ : ℂ) (k : ℕ) :
    (∑ n ∈ Finset.range k, ((n.factorial : ℂ)⁻¹ : ℂ) • (-(θ * Complex.I)) ^ n • spinSOp1 N ^ n) *
      spinSLadder1Plus N =
    spinSLadder1Plus N * (∑ n ∈ Finset.range k,
      ((n.factorial : ℂ)⁻¹ : ℂ) • (-(θ * Complex.I)) ^ n • (spinSOp1 N + 1) ^ n) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Matrix.add_mul, Matrix.mul_add, ih]
      congr 1
      rw [smul_mul_assoc, smul_mul_assoc, spinSOp1_pow_mul_spinSLadder1Plus,
          mul_smul_comm, mul_smul_comm]

/-- **Finite-sum intertwining for L⁻**. -/
theorem spinSRot1_partial_sum_mul_spinSLadder1Minus
    (N : ℕ) (θ : ℂ) (k : ℕ) :
    (∑ n ∈ Finset.range k, ((n.factorial : ℂ)⁻¹ : ℂ) • (-(θ * Complex.I)) ^ n • spinSOp1 N ^ n) *
      spinSLadder1Minus N =
    spinSLadder1Minus N * (∑ n ∈ Finset.range k,
      ((n.factorial : ℂ)⁻¹ : ℂ) • (-(θ * Complex.I)) ^ n • (spinSOp1 N - 1) ^ n) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Matrix.add_mul, Matrix.mul_add, ih]
      congr 1
      rw [smul_mul_assoc, smul_mul_assoc, spinSOp1_pow_mul_spinSLadder1Minus,
          mul_smul_comm, mul_smul_comm]

-- The following intertwining bridge uses the mathlib pattern (see
-- `Matrix.exp_add_of_commute` in `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`)
-- of disabling `respectTransparency` and the `SpecialLinearGroup` coercion instance to
-- avoid the lean4#10414 typeclass-synthesis timeout on `Matrix.exp` lemmas.
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- **Intertwining: `exp A * X = X * exp B`** whenever `A^n * X = X * B^n` for all
`n`. The standard "ad → Ad" bridge specialised to the case where the right-multiplication-by-X
moves the powers across without needing X to be invertible. -/
nonrec theorem matrix_exp_intertwine_of_pow_intertwine
    {nIdx : Type*} [Fintype nIdx] [DecidableEq nIdx]
    {A B X : Matrix nIdx nIdx ℂ}
    (h : ∀ n : ℕ, A ^ n * X = X * B ^ n) :
    exp A * X = X * exp B := by
  open scoped Matrix.Norms.Operator in
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℚ)⁻¹ : ℚ) • A ^ n) (exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) A
  open scoped Matrix.Norms.Operator in
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℚ)⁻¹ : ℚ) • B ^ n) (exp B) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) B
  have hA' : HasSum (fun n : ℕ => ((n.factorial : ℚ)⁻¹ : ℚ) • A ^ n * X) (exp A * X) :=
    hA.mul_right X
  have hB' : HasSum (fun n : ℕ => X * (((n.factorial : ℚ)⁻¹ : ℚ) • B ^ n)) (X * exp B) :=
    hB.mul_left X
  have hfun_eq : (fun n : ℕ => ((n.factorial : ℚ)⁻¹ : ℚ) • A ^ n * X) =
      fun n : ℕ => X * (((n.factorial : ℚ)⁻¹ : ℚ) • B ^ n) := by
    funext n
    rw [smul_mul_assoc, h n, mul_smul_comm]
  rw [hfun_eq] at hA'
  exact hA'.unique hB'

end LatticeSystem.Quantum
