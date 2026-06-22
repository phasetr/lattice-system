import LatticeSystem.Quantum.SpinS.SpinSRotation1
import LatticeSystem.Quantum.SpinS.AxisSwapGaugeEquiv
import LatticeSystem.Quantum.SpinS.Hermitian
import LatticeSystem.Quantum.SpinS.CyclicCommutator
import LatticeSystem.Quantum.SpinS.CyclicCommutator31
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStructuralGeneralN
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergAxisSwapMinEigenvalue
import LatticeSystem.Quantum.SpinS.BareAnisotropicEigLeTwoConditional
import LatticeSystem.Quantum.SpinS.SubmatrixSimpleEigLeTwo
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# General spin-S axis-swap unitary: rotation machinery (foundation)

Foundational layer extracted from `AxisSwapUnitarySSpinS.lean` for build speed
(Tasaki §2.5 Theorem 2.4, Issue #3739).  This file develops the `spinSRot1 N (π/2)`
half-turn rotation machinery — the `exp(-iπ Ŝ¹/2)` conjugation of the spin operators
`Ŝ²`, `Ŝ³`, `Ŝ¹` and ladder operators — assembling the concrete `axisSwapUnitarySSpinS N`
instance witnessing the `AxisSwapUnitaryS N` interface for every `N`.

The eigenspace finrank-`≤ 2` consequences of the axis-swap degeneracy are kept in the
capstone module `AxisSwapUnitarySSpinS.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §2.5 Theorem 2.4, pp. 43–44.
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

/-- **Auxiliary**: `(α • A)^n * X = X * (α • B)^n` follows from `A^n * X = X * B^n` for any
scalar `α`. -/
theorem pow_smul_mul_of_pow_mul
    {nIdx : Type*} [Fintype nIdx] [DecidableEq nIdx]
    {A B X : Matrix nIdx nIdx ℂ} (α : ℂ)
    (h : ∀ n : ℕ, A ^ n * X = X * B ^ n) (n : ℕ) :
    (α • A) ^ n * X = X * (α • B) ^ n := by
  rw [smul_pow, smul_pow, smul_mul_assoc, h n, mul_smul_comm]

-- `spinSRot1` action on L⁺: `exp(α Ŝ¹) L⁺ = L⁺ exp(α (Ŝ¹+1))` for any scalar `α`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_mul_spinSLadder1Plus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp1 N) * spinSLadder1Plus N =
      spinSLadder1Plus N * NormedSpace.exp (α • (spinSOp1 N + 1)) :=
  matrix_exp_intertwine_of_pow_intertwine
    (pow_smul_mul_of_pow_mul α (spinSOp1_pow_mul_spinSLadder1Plus N))

-- `spinSRot1` action on L⁻: `exp(α Ŝ¹) L⁻ = L⁻ exp(α (Ŝ¹-1))`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_mul_spinSLadder1Minus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp1 N) * spinSLadder1Minus N =
      spinSLadder1Minus N * NormedSpace.exp (α • (spinSOp1 N - 1)) :=
  matrix_exp_intertwine_of_pow_intertwine
    (pow_smul_mul_of_pow_mul α (spinSOp1_pow_mul_spinSLadder1Minus N))

-- Auxiliary: scalar-matrix exponential `exp(c • 1) = Complex.exp c • 1`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_one_eq (n : ℕ) (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      Complex.exp c • 1 := by
  have hdiag : (c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      Matrix.diagonal (fun _ => c) := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [hdiag, Matrix.exp_diagonal]
  ext i j
  by_cases h : i = j
  · simp only [h, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
               smul_eq_mul, mul_one, Pi.exp_def]
    rw [← Complex.exp_eq_exp_ℂ]
  · simp [h, Matrix.smul_apply, Matrix.one_apply_ne h]

-- `exp(α • (Ŝ¹ + 1)) = Complex.exp α • exp(α • Ŝ¹)`. Combines additivity
-- (since `α•Ŝ¹` and `α•1` commute) with the scalar-matrix exp formula.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_succ (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • (spinSOp1 N + 1)) =
      Complex.exp α • NormedSpace.exp (α • spinSOp1 N) := by
  have hcomm : Commute (α • spinSOp1 N) (α • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)) :=
    (Commute.one_right (spinSOp1 N)).smul_left α |>.smul_right α
  rw [show α • (spinSOp1 N + 1) = α • spinSOp1 N + α • 1 from smul_add _ _ _]
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one_eq]
  rw [Matrix.mul_smul, Matrix.mul_one]

-- `exp(α • (Ŝ¹ - 1)) = Complex.exp (-α) • exp(α • Ŝ¹)`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_pred (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • (spinSOp1 N - 1)) =
      Complex.exp (-α) • NormedSpace.exp (α • spinSOp1 N) := by
  have hcomm : Commute (α • spinSOp1 N) ((-α) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)) :=
    (Commute.one_right (spinSOp1 N)).smul_left α |>.smul_right (-α)
  rw [show α • (spinSOp1 N - 1) = α • spinSOp1 N + (-α) • 1 from by
    rw [smul_sub, neg_smul]; abel]
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one_eq,
      Matrix.mul_smul, Matrix.mul_one]

-- Inverse pair `exp(α Ŝ¹) exp(-α Ŝ¹) = 1`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_mul_neg (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp1 N) * NormedSpace.exp ((-α) • spinSOp1 N) = 1 := by
  have hcomm : Commute (α • spinSOp1 N) ((-α) • spinSOp1 N) :=
    (Commute.refl (spinSOp1 N)).smul_left α |>.smul_right (-α)
  rw [← Matrix.exp_add_of_commute _ _ hcomm,
      show α • spinSOp1 N + (-α) • spinSOp1 N = (0 : Matrix _ _ ℂ) by
        rw [← add_smul, add_neg_cancel, zero_smul]]
  exact NormedSpace.exp_zero

-- Conjugation L⁺: `exp(α Ŝ¹) L⁺ exp(-α Ŝ¹) = Complex.exp α • L⁺`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_conj_spinSLadder1Plus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp1 N) * spinSLadder1Plus N *
      NormedSpace.exp ((-α) • spinSOp1 N) =
    Complex.exp α • spinSLadder1Plus N := by
  calc NormedSpace.exp (α • spinSOp1 N) * spinSLadder1Plus N *
          NormedSpace.exp ((-α) • spinSOp1 N)
      = spinSLadder1Plus N * NormedSpace.exp (α • (spinSOp1 N + 1)) *
          NormedSpace.exp ((-α) • spinSOp1 N) := by
        rw [exp_smul_spinSOp1_mul_spinSLadder1Plus]
    _ = spinSLadder1Plus N * (Complex.exp α • NormedSpace.exp (α • spinSOp1 N)) *
          NormedSpace.exp ((-α) • spinSOp1 N) := by
        rw [exp_smul_spinSOp1_succ]
    _ = Complex.exp α • (spinSLadder1Plus N * NormedSpace.exp (α • spinSOp1 N) *
          NormedSpace.exp ((-α) • spinSOp1 N)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = Complex.exp α • (spinSLadder1Plus N *
          (NormedSpace.exp (α • spinSOp1 N) * NormedSpace.exp ((-α) • spinSOp1 N))) := by
        rw [Matrix.mul_assoc]
    _ = Complex.exp α • (spinSLadder1Plus N * 1) := by
        rw [exp_smul_spinSOp1_mul_neg]
    _ = Complex.exp α • spinSLadder1Plus N := by
        rw [Matrix.mul_one]

-- Conjugation L⁻: `exp(α Ŝ¹) L⁻ exp(-α Ŝ¹) = Complex.exp (-α) • L⁻`.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_smul_spinSOp1_conj_spinSLadder1Minus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp1 N) * spinSLadder1Minus N *
      NormedSpace.exp ((-α) • spinSOp1 N) =
    Complex.exp (-α) • spinSLadder1Minus N := by
  calc NormedSpace.exp (α • spinSOp1 N) * spinSLadder1Minus N *
          NormedSpace.exp ((-α) • spinSOp1 N)
      = spinSLadder1Minus N * NormedSpace.exp (α • (spinSOp1 N - 1)) *
          NormedSpace.exp ((-α) • spinSOp1 N) := by
        rw [exp_smul_spinSOp1_mul_spinSLadder1Minus]
    _ = spinSLadder1Minus N * (Complex.exp (-α) • NormedSpace.exp (α • spinSOp1 N)) *
          NormedSpace.exp ((-α) • spinSOp1 N) := by
        rw [exp_smul_spinSOp1_pred]
    _ = Complex.exp (-α) • (spinSLadder1Minus N * NormedSpace.exp (α • spinSOp1 N) *
          NormedSpace.exp ((-α) • spinSOp1 N)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = Complex.exp (-α) • (spinSLadder1Minus N *
          (NormedSpace.exp (α • spinSOp1 N) * NormedSpace.exp ((-α) • spinSOp1 N))) := by
        rw [Matrix.mul_assoc]
    _ = Complex.exp (-α) • (spinSLadder1Minus N * 1) := by
        rw [exp_smul_spinSOp1_mul_neg]
    _ = Complex.exp (-α) • spinSLadder1Minus N := by
        rw [Matrix.mul_one]

-- `spinSRot1` conjugation of L⁺ specialised to θ.
theorem spinSRot1_conj_spinSLadder1Plus (N : ℕ) (θ : ℝ) :
    spinSRot1 N θ * spinSLadder1Plus N * spinSRot1 N (-θ) =
      Complex.exp (-((θ : ℂ) * Complex.I)) • spinSLadder1Plus N := by
  unfold spinSRot1
  convert exp_smul_spinSOp1_conj_spinSLadder1Plus N (-((θ : ℂ) * Complex.I)) using 2
  · push_cast; ring_nf

-- `spinSRot1` conjugation of L⁻ specialised to θ.
theorem spinSRot1_conj_spinSLadder1Minus (N : ℕ) (θ : ℝ) :
    spinSRot1 N θ * spinSLadder1Minus N * spinSRot1 N (-θ) =
      Complex.exp (((θ : ℂ) * Complex.I)) • spinSLadder1Minus N := by
  unfold spinSRot1
  convert exp_smul_spinSOp1_conj_spinSLadder1Minus N (-((θ : ℂ) * Complex.I)) using 2
  · push_cast; ring_nf
  · ring_nf

-- `Complex.exp(-((π/2 : ℝ) : ℂ) * I) = -I` (axis-1 rotation by π/2 about ladder L⁺ scales by -i).
theorem cexp_neg_pi_half_mul_I :
    Complex.exp (-(((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) = -Complex.I := by
  rw [show -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
         ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_mul_I]
  simp

-- `Complex.exp(((π/2 : ℝ) : ℂ) * I) = I`.
theorem cexp_pi_half_mul_I :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I]
  simp

-- Conjugation of Ŝ² at θ = π/2: `spinSRot1 N (π/2) * Ŝ² * spinSRot1 N (-π/2) = Ŝ³`.
theorem spinSRot1_pi_half_conj_spinSOp2 (N : ℕ) :
    spinSRot1 N (Real.pi / 2) * spinSOp2 N * spinSRot1 N (-(Real.pi / 2)) = spinSOp3 N := by
  -- 2 Ŝ² = L⁺ + L⁻ via spinSLadder1Plus_add_Minus.
  -- Therefore 2 • (spinSRot1 Ŝ² spinSRot1) = spinSRot1 (L⁺ + L⁻) spinSRot1 = 2 Ŝ³.
  have h2 : (2 : ℂ) • spinSOp2 N = spinSLadder1Plus N + spinSLadder1Minus N :=
    (spinSLadder1Plus_add_Minus N).symm
  have hL : spinSRot1 N (Real.pi / 2) *
      (spinSLadder1Plus N + spinSLadder1Minus N) * spinSRot1 N (-(Real.pi / 2)) =
      ((2 : ℂ) • spinSOp3 N) := by
    rw [Matrix.mul_add, Matrix.add_mul,
        spinSRot1_conj_spinSLadder1Plus, spinSRot1_conj_spinSLadder1Minus,
        cexp_neg_pi_half_mul_I, cexp_pi_half_mul_I]
    -- -I • (Ŝ² + I Ŝ³) + I • (Ŝ² - I Ŝ³) = 2 Ŝ³
    unfold spinSLadder1Plus spinSLadder1Minus
    match_scalars
    all_goals (try simp); try ring
  -- Now `2 • (spinSRot1 Ŝ² spinSRot1) = 2 Ŝ³`, so cancel the 2.
  have hcancel : (2 : ℂ) • (spinSRot1 N (Real.pi / 2) * spinSOp2 N *
      spinSRot1 N (-(Real.pi / 2))) = (2 : ℂ) • spinSOp3 N := by
    rw [← hL, ← h2]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  -- Cancel by dividing by 2 (or apply smul-cancel for a non-zero scalar).
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  exact smul_right_injective _ h2ne hcancel

-- Conjugation of Ŝ³ at θ = π/2: `spinSRot1 N (π/2) * Ŝ³ * spinSRot1 N (-π/2) = -Ŝ²`.
theorem spinSRot1_pi_half_conj_spinSOp3 (N : ℕ) :
    spinSRot1 N (Real.pi / 2) * spinSOp3 N * spinSRot1 N (-(Real.pi / 2)) = -spinSOp2 N := by
  -- 2I Ŝ³ = L⁺ - L⁻; so 2I • (spinSRot1 Ŝ³ spinSRot1) = spinSRot1 (L⁺ - L⁻) spinSRot1 = -2I Ŝ².
  have h2I : (2 * Complex.I) • spinSOp3 N = spinSLadder1Plus N - spinSLadder1Minus N :=
    (spinSLadder1Plus_sub_Minus N).symm
  have hL : spinSRot1 N (Real.pi / 2) *
      (spinSLadder1Plus N - spinSLadder1Minus N) * spinSRot1 N (-(Real.pi / 2)) =
      ((2 * Complex.I) • (-spinSOp2 N)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul,
        spinSRot1_conj_spinSLadder1Plus, spinSRot1_conj_spinSLadder1Minus,
        cexp_neg_pi_half_mul_I, cexp_pi_half_mul_I]
    unfold spinSLadder1Plus spinSLadder1Minus
    match_scalars
    all_goals (try simp); try ring
  have hcancel : (2 * Complex.I) • (spinSRot1 N (Real.pi / 2) * spinSOp3 N *
      spinSRot1 N (-(Real.pi / 2))) = (2 * Complex.I) • (-spinSOp2 N) := by
    rw [← hL, ← h2I]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2Ine : (2 * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero]
  exact smul_right_injective _ h2Ine hcancel

-- Conjugation of Ŝ¹ at θ = π/2: `spinSRot1 N (π/2) * Ŝ¹ * spinSRot1 N (-π/2) = Ŝ¹`
-- (since Ŝ¹ commutes with spinSRot1).
theorem spinSRot1_pi_half_conj_spinSOp1 (N : ℕ) :
    spinSRot1 N (Real.pi / 2) * spinSOp1 N * spinSRot1 N (-(Real.pi / 2)) = spinSOp1 N := by
  have hcomm := spinSRot1_commute_spinSOp1 N (Real.pi / 2)
  rw [show spinSRot1 N (Real.pi / 2) * spinSOp1 N = spinSOp1 N * spinSRot1 N (Real.pi / 2) from
        hcomm,
      Matrix.mul_assoc, spinSRot1_mul_neg, Matrix.mul_one]

/-- **General spin-S axis-swap unitary** — the `π/2` rotation about spin-axis 1.
This is the central object of the Tasaki §2.5 Theorem 2.4 obligation (1) general spin-S
gauge transformation: it fixes Ŝ¹, sends Ŝ² ↦ Ŝ³, and Ŝ³ ↦ −Ŝ². At N = 1 this specialises
to `axisSwapUnitarySpinHalf`. -/
noncomputable def axisSwapUnitarySSpinS (N : ℕ) : AxisSwapUnitaryS N where
  U := spinSRot1 N (Real.pi / 2)
  Uinv := spinSRot1 N (-(Real.pi / 2))
  U_mul_Uinv := spinSRot1_mul_neg N (Real.pi / 2)
  Uinv_mul_U := spinSRot1_neg_mul N (Real.pi / 2)
  conj_spinSOp1 := spinSRot1_pi_half_conj_spinSOp1 N
  conj_spinSOp2 := spinSRot1_pi_half_conj_spinSOp2 N
  conj_spinSOp3 := spinSRot1_pi_half_conj_spinSOp3 N
end LatticeSystem.Quantum
