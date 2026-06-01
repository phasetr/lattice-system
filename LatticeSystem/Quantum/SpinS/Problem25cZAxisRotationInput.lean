import LatticeSystem.Quantum.SpinS.Problem25cTwoSymmetryAxisInput
import LatticeSystem.Quantum.SpinS.PMAsOneTwo

/-!
# Tasaki Problem 2.5.c: z-axis rotation input

This module instantiates the second abstract unitary input from
`Problem25cTwoSymmetryAxisInput.lean` by the concrete general spin-`S` rotation
about axis 3 through angle `-π/2`.  The rotation conjugates `Ŝ²` to `Ŝ¹`, so
the remaining state-side input is invariance under the inverse lifted rotation.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace Complex

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Single-site z-axis rotation -/

/-- **Spin-`S` rotation about axis 3**, `exp(-iθ Ŝ³)`. -/
noncomputable def spinSRot3 (N : ℕ) (θ : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  exp (-(((θ : ℂ) * Complex.I)) • spinSOp3 N)

/-- **At `θ = 0`, `exp(0) = 1` for the z-axis spin-`S` rotation. -/
theorem spinSRot3_zero (N : ℕ) : spinSRot3 N 0 = 1 := by
  unfold spinSRot3
  simp

/-- **Addition formula** for z-axis spin-`S` rotations. -/
theorem spinSRot3_mul (N : ℕ) (θ φ : ℝ) :
    spinSRot3 N θ * spinSRot3 N φ = spinSRot3 N (θ + φ) := by
  unfold spinSRot3
  have hcomm : Commute (-(((θ : ℂ) * Complex.I)) • spinSOp3 N)
      (-(((φ : ℂ) * Complex.I)) • spinSOp3 N) := by
    exact (Commute.refl (spinSOp3 N)).smul_left _ |>.smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm]
  congr 1
  push_cast
  module

/-- **Right inverse** for z-axis spin-`S` rotations. -/
theorem spinSRot3_mul_neg (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ * spinSRot3 N (-θ) = 1 := by
  rw [spinSRot3_mul, add_neg_cancel, spinSRot3_zero]

/-- **Left inverse** for z-axis spin-`S` rotations. -/
theorem spinSRot3_neg_mul (N : ℕ) (θ : ℝ) :
    spinSRot3 N (-θ) * spinSRot3 N θ = 1 := by
  rw [spinSRot3_mul, neg_add_cancel, spinSRot3_zero]

/-- **Adjoint formula** for z-axis spin-`S` rotations. -/
theorem spinSRot3_adjoint (N : ℕ) (θ : ℝ) :
    Matrix.conjTranspose (spinSRot3 N θ) = spinSRot3 N (-θ) := by
  unfold spinSRot3
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, (spinSOp3_isHermitian N)]
  congr 1
  push_cast
  simp [Complex.conj_I, mul_comm]

/-! ## Axis-3 ladder conjugation -/

/-- `Ŝ⁺ + Ŝ⁻ = 2 Ŝ¹`. -/
theorem spinSOpPlus_add_Minus_eq_two_smul_spinSOp1 (N : ℕ) :
    spinSOpPlus N + spinSOpMinus N = (2 : ℂ) • spinSOp1 N := by
  rw [spinSOpPlus_eq_one_add_I_smul_two, spinSOpMinus_eq_one_sub_I_smul_two]
  module

/-- `Ŝ⁺ - Ŝ⁻ = 2i Ŝ²`. -/
theorem spinSOpPlus_sub_Minus_eq_twoI_smul_spinSOp2 (N : ℕ) :
    spinSOpPlus N - spinSOpMinus N = (2 * Complex.I) • spinSOp2 N := by
  rw [spinSOpPlus_eq_one_add_I_smul_two, spinSOpMinus_eq_one_sub_I_smul_two]
  module

/-- **Eigenvector commutation for `Ŝ⁺`**:
`Ŝ³ Ŝ⁺ = Ŝ⁺ (Ŝ³ + 1)`. -/
theorem spinSOp3_mul_spinSOpPlus_shift (N : ℕ) :
    spinSOp3 N * spinSOpPlus N = spinSOpPlus N * (spinSOp3 N + 1) := by
  have h := spinSOp3_commutator_spinSOpPlus N
  calc
    spinSOp3 N * spinSOpPlus N =
        (spinSOp3 N * spinSOpPlus N - spinSOpPlus N * spinSOp3 N) +
          spinSOpPlus N * spinSOp3 N := by
      abel
    _ = spinSOpPlus N + spinSOpPlus N * spinSOp3 N := by
      rw [h]
    _ = spinSOpPlus N * (spinSOp3 N + 1) := by
      rw [Matrix.mul_add, Matrix.mul_one]
      abel

/-- **Eigenvector commutation for `Ŝ⁻`**:
`Ŝ³ Ŝ⁻ = Ŝ⁻ (Ŝ³ - 1)`. -/
theorem spinSOp3_mul_spinSOpMinus_shift (N : ℕ) :
    spinSOp3 N * spinSOpMinus N = spinSOpMinus N * (spinSOp3 N - 1) := by
  have h := spinSOp3_commutator_spinSOpMinus N
  calc
    spinSOp3 N * spinSOpMinus N =
        (spinSOp3 N * spinSOpMinus N - spinSOpMinus N * spinSOp3 N) +
          spinSOpMinus N * spinSOp3 N := by
      abel
    _ = -spinSOpMinus N + spinSOpMinus N * spinSOp3 N := by
      rw [h]
    _ = spinSOpMinus N * (spinSOp3 N - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel

/-- **Iterated commutation for `Ŝ⁺`**:
`(Ŝ³)^n Ŝ⁺ = Ŝ⁺ (Ŝ³ + 1)^n`. -/
theorem spinSOp3_pow_mul_spinSOpPlus (N n : ℕ) :
    spinSOp3 N ^ n * spinSOpPlus N =
      spinSOpPlus N * (spinSOp3 N + 1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, spinSOp3_mul_spinSOpPlus_shift,
          ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

/-- **Iterated commutation for `Ŝ⁻`**:
`(Ŝ³)^n Ŝ⁻ = Ŝ⁻ (Ŝ³ - 1)^n`. -/
theorem spinSOp3_pow_mul_spinSOpMinus (N n : ℕ) :
    spinSOp3 N ^ n * spinSOpMinus N =
      spinSOpMinus N * (spinSOp3 N - 1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, spinSOp3_mul_spinSOpMinus_shift,
          ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- Exponential intertwining of `Ŝ⁺` for the z-axis spin-`S` rotation generator. -/
nonrec theorem exp_smul_spinSOp3_mul_spinSOpPlus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp3 N) * spinSOpPlus N =
      spinSOpPlus N * NormedSpace.exp (α • (spinSOp3 N + 1)) :=
  matrix_exp_intertwine_of_pow_intertwine
    (pow_smul_mul_of_pow_mul α (spinSOp3_pow_mul_spinSOpPlus N))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- Exponential intertwining of `Ŝ⁻` for the z-axis spin-`S` rotation generator. -/
nonrec theorem exp_smul_spinSOp3_mul_spinSOpMinus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp3 N) * spinSOpMinus N =
      spinSOpMinus N * NormedSpace.exp (α • (spinSOp3 N - 1)) :=
  matrix_exp_intertwine_of_pow_intertwine
    (pow_smul_mul_of_pow_mul α (spinSOp3_pow_mul_spinSOpMinus N))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- `exp(α • (Ŝ³ + 1)) = exp(α) • exp(α • Ŝ³)`. -/
nonrec theorem exp_smul_spinSOp3_succ (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • (spinSOp3 N + 1)) =
      Complex.exp α • NormedSpace.exp (α • spinSOp3 N) := by
  have hcomm : Commute (α • spinSOp3 N) (α • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
    (Commute.one_right (spinSOp3 N)).smul_left α |>.smul_right α
  rw [show α • (spinSOp3 N + 1) = α • spinSOp3 N + α • 1 from smul_add _ _ _]
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one_eq]
  rw [Matrix.mul_smul, Matrix.mul_one]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- `exp(α • (Ŝ³ - 1)) = exp(-α) • exp(α • Ŝ³)`. -/
nonrec theorem exp_smul_spinSOp3_pred (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • (spinSOp3 N - 1)) =
      Complex.exp (-α) • NormedSpace.exp (α • spinSOp3 N) := by
  have hcomm : Commute (α • spinSOp3 N) ((-α) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
    (Commute.one_right (spinSOp3 N)).smul_left α |>.smul_right (-α)
  rw [show α • (spinSOp3 N - 1) = α • spinSOp3 N + (-α) • 1 from by
    rw [smul_sub, neg_smul]; abel]
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one_eq,
      Matrix.mul_smul, Matrix.mul_one]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse pair `exp(α Ŝ³) exp(-α Ŝ³) = 1`. -/
nonrec theorem exp_smul_spinSOp3_mul_neg (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp3 N) * NormedSpace.exp ((-α) • spinSOp3 N) = 1 := by
  have hcomm : Commute (α • spinSOp3 N) ((-α) • spinSOp3 N) :=
    (Commute.refl (spinSOp3 N)).smul_left α |>.smul_right (-α)
  rw [← Matrix.exp_add_of_commute _ _ hcomm,
      show α • spinSOp3 N + (-α) • spinSOp3 N = (0 : Matrix _ _ ℂ) by
        rw [← add_smul, add_neg_cancel, zero_smul]]
  exact NormedSpace.exp_zero

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugation of `Ŝ⁺` by the z-axis exponential. -/
nonrec theorem exp_smul_spinSOp3_conj_spinSOpPlus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp3 N) * spinSOpPlus N *
      NormedSpace.exp ((-α) • spinSOp3 N) =
    Complex.exp α • spinSOpPlus N := by
  calc NormedSpace.exp (α • spinSOp3 N) * spinSOpPlus N *
          NormedSpace.exp ((-α) • spinSOp3 N)
      = spinSOpPlus N * NormedSpace.exp (α • (spinSOp3 N + 1)) *
          NormedSpace.exp ((-α) • spinSOp3 N) := by
        rw [exp_smul_spinSOp3_mul_spinSOpPlus]
    _ = spinSOpPlus N * (Complex.exp α • NormedSpace.exp (α • spinSOp3 N)) *
          NormedSpace.exp ((-α) • spinSOp3 N) := by
        rw [exp_smul_spinSOp3_succ]
    _ = Complex.exp α • (spinSOpPlus N * NormedSpace.exp (α • spinSOp3 N) *
          NormedSpace.exp ((-α) • spinSOp3 N)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = Complex.exp α • (spinSOpPlus N *
          (NormedSpace.exp (α • spinSOp3 N) * NormedSpace.exp ((-α) • spinSOp3 N))) := by
        rw [Matrix.mul_assoc]
    _ = Complex.exp α • (spinSOpPlus N * 1) := by
        rw [exp_smul_spinSOp3_mul_neg]
    _ = Complex.exp α • spinSOpPlus N := by
        rw [Matrix.mul_one]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugation of `Ŝ⁻` by the z-axis exponential. -/
nonrec theorem exp_smul_spinSOp3_conj_spinSOpMinus (N : ℕ) (α : ℂ) :
    NormedSpace.exp (α • spinSOp3 N) * spinSOpMinus N *
      NormedSpace.exp ((-α) • spinSOp3 N) =
    Complex.exp (-α) • spinSOpMinus N := by
  calc NormedSpace.exp (α • spinSOp3 N) * spinSOpMinus N *
          NormedSpace.exp ((-α) • spinSOp3 N)
      = spinSOpMinus N * NormedSpace.exp (α • (spinSOp3 N - 1)) *
          NormedSpace.exp ((-α) • spinSOp3 N) := by
        rw [exp_smul_spinSOp3_mul_spinSOpMinus]
    _ = spinSOpMinus N * (Complex.exp (-α) • NormedSpace.exp (α • spinSOp3 N)) *
          NormedSpace.exp ((-α) • spinSOp3 N) := by
        rw [exp_smul_spinSOp3_pred]
    _ = Complex.exp (-α) • (spinSOpMinus N * NormedSpace.exp (α • spinSOp3 N) *
          NormedSpace.exp ((-α) • spinSOp3 N)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = Complex.exp (-α) • (spinSOpMinus N *
          (NormedSpace.exp (α • spinSOp3 N) * NormedSpace.exp ((-α) • spinSOp3 N))) := by
        rw [Matrix.mul_assoc]
    _ = Complex.exp (-α) • (spinSOpMinus N * 1) := by
        rw [exp_smul_spinSOp3_mul_neg]
    _ = Complex.exp (-α) • spinSOpMinus N := by
        rw [Matrix.mul_one]

/-- `spinSRot3` conjugation of `Ŝ⁺`. -/
theorem spinSRot3_conj_spinSOpPlus (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ * spinSOpPlus N * spinSRot3 N (-θ) =
      Complex.exp (-((θ : ℂ) * Complex.I)) • spinSOpPlus N := by
  unfold spinSRot3
  convert exp_smul_spinSOp3_conj_spinSOpPlus N (-((θ : ℂ) * Complex.I)) using 2
  · push_cast; ring_nf

/-- `spinSRot3` conjugation of `Ŝ⁻`. -/
theorem spinSRot3_conj_spinSOpMinus (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ * spinSOpMinus N * spinSRot3 N (-θ) =
      Complex.exp (((θ : ℂ) * Complex.I)) • spinSOpMinus N := by
  unfold spinSRot3
  convert exp_smul_spinSOp3_conj_spinSOpMinus N (-((θ : ℂ) * Complex.I)) using 2
  · push_cast
    ring_nf
  · congr 1
    ring_nf

/-- `exp(iπ/2) = i`. -/
theorem cexp_neg_neg_pi_half_mul_I :
    Complex.exp (-(((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I)) = Complex.I := by
  rw [show -(((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) =
         (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      cexp_pi_half_mul_I]

/-- `exp(-iπ/2) = -i`. -/
theorem cexp_neg_pi_half_mul_I' :
    Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I)) = -Complex.I := by
  rw [show (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) =
         -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      cexp_neg_pi_half_mul_I]

/-- The `-π/2` z-axis spin-`S` rotation conjugates `Ŝ²` to `Ŝ¹`. -/
theorem spinSRot3_neg_pi_half_conj_spinSOp2 (N : ℕ) :
    spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N * spinSRot3 N (Real.pi / 2) =
      spinSOp1 N := by
  have h2I : (2 * Complex.I) • spinSOp2 N = spinSOpPlus N - spinSOpMinus N :=
    (spinSOpPlus_sub_Minus_eq_twoI_smul_spinSOp2 N).symm
  have hL : spinSRot3 N (-(Real.pi / 2)) *
      (spinSOpPlus N - spinSOpMinus N) * spinSRot3 N (Real.pi / 2) =
      ((2 * Complex.I) • spinSOp1 N) := by
    have hplus :
        spinSRot3 N (-(Real.pi / 2)) * spinSOpPlus N * spinSRot3 N (Real.pi / 2) =
          Complex.I • spinSOpPlus N := by
      simpa [cexp_neg_neg_pi_half_mul_I, show -(-(Real.pi / 2)) = (Real.pi / 2 : ℝ) by ring]
        using spinSRot3_conj_spinSOpPlus N (-(Real.pi / 2))
    have hminus :
        spinSRot3 N (-(Real.pi / 2)) * spinSOpMinus N * spinSRot3 N (Real.pi / 2) =
          -(Complex.I • spinSOpMinus N) := by
      have hraw := spinSRot3_conj_spinSOpMinus N (-(Real.pi / 2))
      have hcexp :
          Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I)) = -Complex.I :=
        cexp_neg_pi_half_mul_I'
      rw [hcexp] at hraw
      simpa [neg_smul, show -(-(Real.pi / 2)) = (Real.pi / 2 : ℝ) by ring] using hraw
    rw [Matrix.mul_sub, Matrix.sub_mul, hplus, hminus]
    calc
      Complex.I • spinSOpPlus N - -(Complex.I • spinSOpMinus N) =
          Complex.I • (spinSOpPlus N + spinSOpMinus N) := by
        module
      _ = Complex.I • ((2 : ℂ) • spinSOp1 N) := by
        rw [spinSOpPlus_add_Minus_eq_two_smul_spinSOp1]
      _ = (2 * Complex.I) • spinSOp1 N := by
        module
  have hcancel : (2 * Complex.I) • (spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N *
      spinSRot3 N (Real.pi / 2)) = (2 * Complex.I) • spinSOp1 N := by
    rw [← hL, ← h2I]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2Ine : (2 * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero]
  exact smul_right_injective _ h2Ine hcancel

/-! ## Lifted Problem 2.5.c input -/

/-- The lifted `-π/2` z-axis rotation conjugates the single-site axis-2
component to the axis-1 component. -/
theorem manyBodySpinSRot3_neg_pi_half_conj_onSiteS_spinSOp2
    (x : V) :
    manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2))) *
        onSiteS x (spinSOp2 N) *
        manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)) =
      onSiteS x (spinSOp1 N) := by
  simpa [show -(-(Real.pi / 2)) = (Real.pi / 2 : ℝ) by ring,
    spinSRot3_neg_pi_half_conj_spinSOp2] using
    (manyBodyTensorS_conj_onSiteS (Λ := V) (N := N)
      (spinSRot3_mul_neg N (-(Real.pi / 2))) x (spinSOp2 N))

omit [DecidableEq V] in
/-- The lifted `-π/2` z-axis rotation has lifted inverse `π/2` as its adjoint. -/
theorem manyBodySpinSRot3_neg_pi_half_conjTranspose
    (V : Type*) [Fintype V] (N : ℕ) :
    (manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2)))).conjTranspose =
      manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)) := by
  simpa [spinSRot3_adjoint] using
    (manyBodyTensorS_conjTranspose (V := V) (N := N)
      (fun _ : V => spinSRot3 N (-(Real.pi / 2))))

/-- If a normalized state is fixed by both the lifted axis-swap inverse and the
inverse lifted z-axis rotation, then all three squared single-site spin
expectations have value `N(N+2)/12`. -/
theorem singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_zAxisRot
    (x : V) {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = Φ)
    (hΦrot :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec Φ = Φ) :
    singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ =
        (N : ℂ) * (N + 2) / 12 ∧
      singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ =
        (N : ℂ) * (N + 2) / 12 :=
  singleSiteSpinSquareExpectationS_all_axes_eq_of_axisSwapInvariant_unitary_axis12
    (x := x)
    (T := manyBodyTensorS (fun _ : V => spinSRot3 N (-(Real.pi / 2))))
    (Tinv := manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
    hΦnorm hΦswap
    (manyBodySpinSRot3_neg_pi_half_conjTranspose V N)
    (by
      rw [manyBodyTensorS_mul]
      simpa [spinSRot3_mul_neg] using manyBodyTensorS_one (Λ := V) (N := N))
    hΦrot
    (manyBodySpinSRot3_neg_pi_half_conj_onSiteS_spinSOp2 (x := x))

end LatticeSystem.Quantum
