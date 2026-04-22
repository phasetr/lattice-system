/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalfRotation

/-!
# SpinHalfRotation conjugation, exp form, coherent state, Hadamard

The conjugation / general-θ / matrix exp / Hadamard layers
above the rotation operator definitions:
- General-θ conjugation (Tasaki eq. (2.1.16)),
- Same-axis invariance (Tasaki eq. (2.1.15)),
- π/2 rotation conjugation (Tasaki eq. (2.1.22)),
- Equivalence with matrix exponential (Tasaki Problem 2.1.b),
- Coherent state (Tasaki §2.1 Problem 2.1.d),
- Problem 2.1.e (phase factor at θ = φ = π/2),
- Vector inner product `Ŝ · v` (Tasaki eq. (2.1.19)),
- Hadamard matrix (basis change between σ^x and σ^z),
- y-axis diagonalizer (basis change between σ^y and σ^z).

(Refactor Phase 2 PR 22 — first SpinHalfRotation extraction,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## General-θ conjugation (Tasaki eq (2.1.16))

For distinct axes the closed-form rotation conjugates the spin operator
by the standard rotation matrix: `(Û^(α)_θ)† · Ŝ^(β) · Û^(α)_θ =
cos(θ)·Ŝ^(β) - sin(θ)·Ŝ^(γ)`, where `(α, β, γ)` is cyclic.
-/

/-- Expansion of the general-θ conjugation as an algebraic identity.
For `Sα` Hermitian with `Sα² = (1/4)·1`, anticommuting with `Sβ`, and
with commutator `[Sα, Sβ] = I·Sγ`, we have
`(rotOf Sα θ)ᴴ · Sβ · rotOf Sα θ = cos(θ)·Sβ - sin(θ)·Sγ`. -/
private lemma rotOf_conj_of_ne
    {Sα Sβ Sγ : Matrix (Fin 2) (Fin 2) ℂ}
    (hα : Sα.IsHermitian) (hα_sq : Sα * Sα = (1 / 4 : ℂ) • 1)
    (hanti : Sα * Sβ + Sβ * Sα = 0)
    (hcomm : Sα * Sβ - Sβ * Sα = Complex.I • Sγ)
    (θ : ℝ) :
    (rotOf Sα θ)ᴴ * Sβ * rotOf Sα θ =
      (Real.cos θ : ℂ) • Sβ - (Real.sin θ : ℂ) • Sγ := by
  have htriple : Sα * Sβ * Sα = (-(1 / 4 : ℂ)) • Sβ :=
    spinHalfOp_triple_of_anticomm hα_sq hanti
  rw [rotOf_adjoint hα]
  unfold rotOf
  set c := (Real.cos (θ / 2) : ℂ) with hc
  set s := (Real.sin (θ / 2) : ℂ) with hs
  have hcn : (Real.cos (-θ / 2) : ℂ) = c := by
    rw [show (-θ : ℝ) / 2 = -(θ / 2) from by ring, Real.cos_neg]
  have hsn : (Real.sin (-θ / 2) : ℂ) = -s := by
    rw [show (-θ : ℝ) / 2 = -(θ / 2) from by ring]
    simp [Real.sin_neg, hs]
  rw [hcn, hsn]
  rw [show (2 * Complex.I * -s : ℂ) = -(2 * Complex.I * s) from by ring,
      neg_smul, sub_neg_eq_add]
  -- Now goal: (c • 1 + (2*I*s) • Sα) * Sβ * (c • 1 - (2*I*s) • Sα) = cos θ • Sβ - sin θ • Sγ
  set k := (2 * Complex.I * s : ℂ) with hk
  -- Expand via distributivity
  have expand :
      (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + k • Sα) * Sβ *
          (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) - k • Sα) =
        (c * c) • Sβ + (c * k) • (Sα * Sβ) - (c * k) • (Sβ * Sα)
          - (k * k) • (Sα * Sβ * Sα) := by
    rw [add_mul, add_mul, mul_sub, mul_sub]
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
      smul_smul]
    rw [show (k * c : ℂ) = c * k from mul_comm _ _]
    abel
  rw [expand]
  rw [show (c * c) • Sβ + (c * k) • (Sα * Sβ) - (c * k) • (Sβ * Sα) -
        (k * k) • (Sα * Sβ * Sα) =
      (c * c) • Sβ + (c * k) • (Sα * Sβ - Sβ * Sα) -
        (k * k) • (Sα * Sβ * Sα) from by
    rw [smul_sub]; abel]
  rw [hcomm, htriple]
  rw [smul_smul, smul_smul]
  -- Goal: (c*c)•Sβ + (c*k*I)•Sγ - (k*k)•(-(1/4)•Sβ) = cos θ•Sβ - sin θ•Sγ
  -- After smul_smul on -(k*k)•(-(1/4)•Sβ), we'd need two smul_smuls
  -- Actually the -(k*k) has a minus
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [show c * k * Complex.I = -(2 * c * s) from by
    rw [hk]; linear_combination (2 * c * s) * hI2]
  rw [show (k * k : ℂ) = -(4 * (s * s)) from by
    rw [hk]; linear_combination (4 * (s * s)) * hI2]
  -- Simplify the scalar coefficient of Sβ
  rw [show -(4 * (s * s)) * -(1 / 4 : ℂ) = s * s from by ring]
  -- Goal: (c*c)•Sβ + -(2*c*s)•Sγ - (s*s)•Sβ = cos θ•Sβ - sin θ•Sγ
  have hcos : (Real.cos θ : ℂ) = c * c - s * s := by
    change (Real.cos θ : ℂ) = (Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)
      - (Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)
    have hcos' : Real.cos θ = (Real.cos (θ / 2))^2 - (Real.sin (θ / 2))^2 := by
      rw [show θ = 2 * (θ / 2) from by ring, Real.cos_two_mul,
        show (1 : ℝ) = (Real.cos (θ / 2))^2 + (Real.sin (θ / 2))^2 from
          (Real.cos_sq_add_sin_sq _).symm]
      ring
    rw [hcos']
    push_cast; ring
  have hsin : (Real.sin θ : ℂ) = 2 * c * s := by
    change (Real.sin θ : ℂ) =
      2 * (Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)
    rw [show θ = 2 * (θ / 2) from by ring, Real.sin_two_mul]
    push_cast; ring
  rw [hcos, hsin]
  rw [sub_smul, neg_smul]
  abel

/-- `(Û^(1)_θ)† · Ŝ^(2) · Û^(1)_θ = cos(θ)·Ŝ^(2) - sin(θ)·Ŝ^(3)`. -/
theorem spinHalfRot1_conj_spinHalfOp2 (θ : ℝ) :
    (spinHalfRot1 θ)ᴴ * spinHalfOp2 * spinHalfRot1 θ =
      (Real.cos θ : ℂ) • spinHalfOp2 - (Real.sin θ : ℂ) • spinHalfOp3 :=
  rotOf_conj_of_ne spinHalfOp1_isHermitian spinHalfOp1_mul_self
    spinHalfOp1_anticomm_spinHalfOp2
    spinHalfOp1_commutator_spinHalfOp2 θ

/-- `(Û^(2)_θ)† · Ŝ^(3) · Û^(2)_θ = cos(θ)·Ŝ^(3) - sin(θ)·Ŝ^(1)`. -/
theorem spinHalfRot2_conj_spinHalfOp3 (θ : ℝ) :
    (spinHalfRot2 θ)ᴴ * spinHalfOp3 * spinHalfRot2 θ =
      (Real.cos θ : ℂ) • spinHalfOp3 - (Real.sin θ : ℂ) • spinHalfOp1 :=
  rotOf_conj_of_ne spinHalfOp2_isHermitian spinHalfOp2_mul_self
    spinHalfOp2_anticomm_spinHalfOp3
    spinHalfOp2_commutator_spinHalfOp3 θ

/-- `(Û^(3)_θ)† · Ŝ^(1) · Û^(3)_θ = cos(θ)·Ŝ^(1) - sin(θ)·Ŝ^(2)`. -/
theorem spinHalfRot3_conj_spinHalfOp1 (θ : ℝ) :
    (spinHalfRot3 θ)ᴴ * spinHalfOp1 * spinHalfRot3 θ =
      (Real.cos θ : ℂ) • spinHalfOp1 - (Real.sin θ : ℂ) • spinHalfOp2 :=
  rotOf_conj_of_ne spinHalfOp3_isHermitian spinHalfOp3_mul_self
    spinHalfOp3_anticomm_spinHalfOp1
    spinHalfOp3_commutator_spinHalfOp1 θ

/-- `(Û^(1)_θ)† · Ŝ^(3) · Û^(1)_θ = cos(θ)·Ŝ^(3) + sin(θ)·Ŝ^(2)`. -/
theorem spinHalfRot1_conj_spinHalfOp3 (θ : ℝ) :
    (spinHalfRot1 θ)ᴴ * spinHalfOp3 * spinHalfRot1 θ =
      (Real.cos θ : ℂ) • spinHalfOp3 + (Real.sin θ : ℂ) • spinHalfOp2 := by
  have hcomm : spinHalfOp1 * spinHalfOp3 - spinHalfOp3 * spinHalfOp1 =
      Complex.I • (-spinHalfOp2) := by
    rw [show spinHalfOp1 * spinHalfOp3 - spinHalfOp3 * spinHalfOp1 =
          -(spinHalfOp3 * spinHalfOp1 - spinHalfOp1 * spinHalfOp3) from by abel,
      spinHalfOp3_commutator_spinHalfOp1, smul_neg]
  have h : (spinHalfRot1 θ)ᴴ * spinHalfOp3 * spinHalfRot1 θ =
      (Real.cos θ : ℂ) • spinHalfOp3 - (Real.sin θ : ℂ) • (-spinHalfOp2) :=
    rotOf_conj_of_ne spinHalfOp1_isHermitian spinHalfOp1_mul_self
      (anticomm_swap spinHalfOp3_anticomm_spinHalfOp1) hcomm θ
  rw [h, smul_neg, sub_neg_eq_add]

/-- `(Û^(2)_θ)† · Ŝ^(1) · Û^(2)_θ = cos(θ)·Ŝ^(1) + sin(θ)·Ŝ^(3)`. -/
theorem spinHalfRot2_conj_spinHalfOp1 (θ : ℝ) :
    (spinHalfRot2 θ)ᴴ * spinHalfOp1 * spinHalfRot2 θ =
      (Real.cos θ : ℂ) • spinHalfOp1 + (Real.sin θ : ℂ) • spinHalfOp3 := by
  have hcomm : spinHalfOp2 * spinHalfOp1 - spinHalfOp1 * spinHalfOp2 =
      Complex.I • (-spinHalfOp3) := by
    rw [show spinHalfOp2 * spinHalfOp1 - spinHalfOp1 * spinHalfOp2 =
          -(spinHalfOp1 * spinHalfOp2 - spinHalfOp2 * spinHalfOp1) from by abel,
      spinHalfOp1_commutator_spinHalfOp2, smul_neg]
  have h : (spinHalfRot2 θ)ᴴ * spinHalfOp1 * spinHalfRot2 θ =
      (Real.cos θ : ℂ) • spinHalfOp1 - (Real.sin θ : ℂ) • (-spinHalfOp3) :=
    rotOf_conj_of_ne spinHalfOp2_isHermitian spinHalfOp2_mul_self
      (anticomm_swap spinHalfOp1_anticomm_spinHalfOp2) hcomm θ
  rw [h, smul_neg, sub_neg_eq_add]

/-- `(Û^(3)_θ)† · Ŝ^(2) · Û^(3)_θ = cos(θ)·Ŝ^(2) + sin(θ)·Ŝ^(1)` (Tasaki (2.1.14)). -/
theorem spinHalfRot3_conj_spinHalfOp2 (θ : ℝ) :
    (spinHalfRot3 θ)ᴴ * spinHalfOp2 * spinHalfRot3 θ =
      (Real.cos θ : ℂ) • spinHalfOp2 + (Real.sin θ : ℂ) • spinHalfOp1 := by
  have hcomm : spinHalfOp3 * spinHalfOp2 - spinHalfOp2 * spinHalfOp3 =
      Complex.I • (-spinHalfOp1) := by
    rw [show spinHalfOp3 * spinHalfOp2 - spinHalfOp2 * spinHalfOp3 =
          -(spinHalfOp2 * spinHalfOp3 - spinHalfOp3 * spinHalfOp2) from by abel,
      spinHalfOp2_commutator_spinHalfOp3, smul_neg]
  have h : (spinHalfRot3 θ)ᴴ * spinHalfOp2 * spinHalfRot3 θ =
      (Real.cos θ : ℂ) • spinHalfOp2 - (Real.sin θ : ℂ) • (-spinHalfOp1) :=
    rotOf_conj_of_ne spinHalfOp3_isHermitian spinHalfOp3_mul_self
      (anticomm_swap spinHalfOp2_anticomm_spinHalfOp3) hcomm θ
  rw [h, smul_neg, sub_neg_eq_add]

/-! ## Same-axis invariance (Tasaki eq (2.1.15))

For same-axis conjugation, `Sα` commutes with `rotOf Sα θ` (since it
commutes with 1 and with itself), so `(rotOf Sα θ)ᴴ · Sα · rotOf Sα θ =
(rotOf Sα θ)ᴴ · rotOf Sα θ · Sα = Sα` via unitarity.
-/

/-- `Sα * rotOf Sα θ = rotOf Sα θ * Sα`: a spin operator commutes with its own rotation. -/
private lemma rotOf_comm_self (Sα : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    Sα * rotOf Sα θ = rotOf Sα θ * Sα := by
  unfold rotOf
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
    Matrix.one_mul, mul_smul_comm, smul_mul_assoc]

/-- `(Û^(1)_θ)† · Ŝ^(1) · Û^(1)_θ = Ŝ^(1)`. -/
theorem spinHalfRot1_conj_spinHalfOp1 (θ : ℝ) :
    (spinHalfRot1 θ)ᴴ * spinHalfOp1 * spinHalfRot1 θ = spinHalfOp1 := by
  rw [spinHalfRot1_adjoint]
  have h : spinHalfOp1 * spinHalfRot1 θ = spinHalfRot1 θ * spinHalfOp1 :=
    rotOf_comm_self spinHalfOp1 θ
  rw [mul_assoc, h, ← mul_assoc]
  rw [spinHalfRot1_mul, show -θ + θ = 0 from by ring, spinHalfRot1_zero,
    Matrix.one_mul]

/-- `(Û^(2)_θ)† · Ŝ^(2) · Û^(2)_θ = Ŝ^(2)`. -/
theorem spinHalfRot2_conj_spinHalfOp2 (θ : ℝ) :
    (spinHalfRot2 θ)ᴴ * spinHalfOp2 * spinHalfRot2 θ = spinHalfOp2 := by
  rw [spinHalfRot2_adjoint]
  have h : spinHalfOp2 * spinHalfRot2 θ = spinHalfRot2 θ * spinHalfOp2 :=
    rotOf_comm_self spinHalfOp2 θ
  rw [mul_assoc, h, ← mul_assoc]
  rw [spinHalfRot2_mul, show -θ + θ = 0 from by ring, spinHalfRot2_zero,
    Matrix.one_mul]

/-- `(Û^(3)_θ)† · Ŝ^(3) · Û^(3)_θ = Ŝ^(3)` (Tasaki eq (2.1.15)). -/
theorem spinHalfRot3_conj_spinHalfOp3 (θ : ℝ) :
    (spinHalfRot3 θ)ᴴ * spinHalfOp3 * spinHalfRot3 θ = spinHalfOp3 := by
  rw [spinHalfRot3_adjoint]
  have h : spinHalfOp3 * spinHalfRot3 θ = spinHalfRot3 θ * spinHalfOp3 :=
    rotOf_comm_self spinHalfOp3 θ
  rw [mul_assoc, h, ← mul_assoc]
  rw [spinHalfRot3_mul, show -θ + θ = 0 from by ring, spinHalfRot3_zero,
    Matrix.one_mul]

/-! ## π/2 rotation conjugation (Tasaki eq (2.1.22))

`(Û^(α)_{π/2})† · Ŝ^(β) · Û^(α)_{π/2} = -ε^{αβγ} · Ŝ^(γ)` for
`(α, β, γ)` cyclic. This is the specialization of (2.1.16) at
`θ = π/2` using `cos(π/2) = 0`, `sin(π/2) = 1`.
-/

/-- `(Û^(1)_{π/2})† · Ŝ^(2) · Û^(1)_{π/2} = -Ŝ^(3)` (ε^{123}=+1). -/
theorem spinHalfRot1_half_pi_conj_spinHalfOp2 :
    (spinHalfRot1 (Real.pi / 2))ᴴ * spinHalfOp2 * spinHalfRot1 (Real.pi / 2) =
      -spinHalfOp3 := by
  rw [spinHalfRot1_conj_spinHalfOp2, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(Û^(2)_{π/2})† · Ŝ^(3) · Û^(2)_{π/2} = -Ŝ^(1)` (ε^{231}=+1). -/
theorem spinHalfRot2_half_pi_conj_spinHalfOp3 :
    (spinHalfRot2 (Real.pi / 2))ᴴ * spinHalfOp3 * spinHalfRot2 (Real.pi / 2) =
      -spinHalfOp1 := by
  rw [spinHalfRot2_conj_spinHalfOp3, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(Û^(3)_{π/2})† · Ŝ^(1) · Û^(3)_{π/2} = -Ŝ^(2)` (ε^{312}=+1). -/
theorem spinHalfRot3_half_pi_conj_spinHalfOp1 :
    (spinHalfRot3 (Real.pi / 2))ᴴ * spinHalfOp1 * spinHalfRot3 (Real.pi / 2) =
      -spinHalfOp2 := by
  rw [spinHalfRot3_conj_spinHalfOp1, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(Û^(1)_{π/2})† · Ŝ^(3) · Û^(1)_{π/2} = Ŝ^(2)` (ε^{132}=-1). -/
theorem spinHalfRot1_half_pi_conj_spinHalfOp3 :
    (spinHalfRot1 (Real.pi / 2))ᴴ * spinHalfOp3 * spinHalfRot1 (Real.pi / 2) =
      spinHalfOp2 := by
  rw [spinHalfRot1_conj_spinHalfOp3, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(Û^(2)_{π/2})† · Ŝ^(1) · Û^(2)_{π/2} = Ŝ^(3)` (ε^{213}=-1). -/
theorem spinHalfRot2_half_pi_conj_spinHalfOp1 :
    (spinHalfRot2 (Real.pi / 2))ᴴ * spinHalfOp1 * spinHalfRot2 (Real.pi / 2) =
      spinHalfOp3 := by
  rw [spinHalfRot2_conj_spinHalfOp1, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(Û^(3)_{π/2})† · Ŝ^(2) · Û^(3)_{π/2} = Ŝ^(1)` (ε^{321}=-1). -/
theorem spinHalfRot3_half_pi_conj_spinHalfOp2 :
    (spinHalfRot3 (Real.pi / 2))ᴴ * spinHalfOp2 * spinHalfRot3 (Real.pi / 2) =
      spinHalfOp1 := by
  rw [spinHalfRot3_conj_spinHalfOp2, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ## Equivalence with matrix exponential (Tasaki Problem 2.1.b)

For the axis-3 case, `-iθ Ŝ^(3)` is diagonal, so
`exp(-iθ Ŝ^(3)) = diag(exp(-iθ/2), exp(iθ/2))` via
`Matrix.exp_diagonal`, and each entry evaluates via Euler's formula
to `cos(θ/2) ∓ i sin(θ/2)`, matching `spinHalfRot3 θ`. -/

/-- `pauliZ = diagonal(1, -1)`. -/
private lemma pauliZ_eq_diagonal :
    pauliZ = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.diagonal]

set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
/-- Problem 2.1.b for axis 3: `Û^(3)_θ = exp(-iθ Ŝ^(3))`. -/
theorem spinHalfRot3_eq_exp (θ : ℝ) :
    spinHalfRot3 θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • spinHalfOp3) := by
  unfold spinHalfRot3 spinHalfOp3 rotOf
  rw [pauliZ_eq_diagonal]
  -- LHS: cos(θ/2)•1 - (2I sin(θ/2)·(1/2)) • diagonal(1,-1)
  -- RHS: exp(-(Iθ) • (1/2) • diagonal(1,-1))
  -- Convert RHS to exp of a diagonal matrix
  conv_rhs =>
    rw [smul_smul, show -(Complex.I * ↑θ) * (1 / 2) = -(Complex.I * ↑θ / 2) from by ring]
    rw [show (-(Complex.I * ↑θ / 2)) •
          (Matrix.diagonal fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) =
        Matrix.diagonal (fun i : Fin 2 =>
          if i = 0 then -(Complex.I * ↑θ / 2)
          else Complex.I * ↑θ / 2) from by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, Matrix.smul_apply]]
    rw [Matrix.exp_diagonal]
  -- Now both sides are element-by-element. Compare entries.
  -- Unify NormedSpace.exp on ℂ with Complex.exp
  have hexp : ∀ z : ℂ, NormedSpace.exp z = Complex.exp z :=
    congr_fun Complex.exp_eq_exp_ℂ.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.diagonal, Matrix.sub_apply, Matrix.smul_apply, hexp]
     <;> first
      | (rw [show -(Complex.I * ↑θ / 2) = (-(↑θ / 2)) * Complex.I from by ring,
            Complex.exp_mul_I]
         simp only [Complex.cos_neg, Complex.sin_neg, neg_mul, mul_neg]
         ring)
      | (rw [show Complex.I * ↑θ / 2 = (↑θ / 2) * Complex.I from by ring,
            Complex.exp_mul_I]
         ring))

/-! ## Coherent state (Tasaki §2.1 Problem 2.1.d) -/

set_option linter.flexible false in
set_option linter.unusedTactic false in
/-- Tasaki Problem 2.1.d: `Û^(3)_φ · Û^(2)_θ · |ψ^↑⟩ =
e^{-iφ/2} cos(θ/2) |ψ^↑⟩ + e^{iφ/2} sin(θ/2) |ψ^↓⟩`. -/
theorem spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp (θ φ : ℝ) :
    (spinHalfRot3 φ * spinHalfRot2 θ).mulVec spinHalfUp =
      ![Complex.exp (-(Complex.I * (φ : ℂ) / 2)) * (Real.cos (θ / 2) : ℂ),
        Complex.exp (Complex.I * (φ : ℂ) / 2) * (Real.sin (θ / 2) : ℂ)] := by
  unfold spinHalfRot3 spinHalfRot2 rotOf spinHalfOp3 spinHalfOp2 pauliZ pauliY
  ext i
  fin_cases i
  · -- case 0: up component
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
       spinHalfUp, Matrix.smul_apply, Matrix.sub_apply]
    rw [show -(Complex.I * (φ : ℂ) / 2) = (-(↑φ / 2)) * Complex.I from by ring,
      Complex.exp_mul_I]
    left
    simp only [Complex.cos_neg, Complex.sin_neg, neg_mul]
    push_cast; ring
  · -- case 1: down component
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
       spinHalfUp, Matrix.smul_apply, Matrix.sub_apply]
    rw [show Complex.I * (φ : ℂ) / 2 = (↑φ / 2) * Complex.I from by ring,
      Complex.exp_mul_I]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination
      -(Complex.sin (↑θ / 2)) *
        (Complex.cos (↑φ / 2) + Complex.I * Complex.sin (↑φ / 2)) * hI

set_option linter.flexible false in
set_option linter.unusedTactic false in
/-- `Û^(3)_φ · Û^(2)_θ · |ψ^↓⟩ =
-e^{-iφ/2} sin(θ/2) |ψ^↑⟩ + e^{iφ/2} cos(θ/2) |ψ^↓⟩`.
Companion to `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp`. -/
theorem spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown (θ φ : ℝ) :
    (spinHalfRot3 φ * spinHalfRot2 θ).mulVec spinHalfDown =
      ![-(Complex.exp (-(Complex.I * (φ : ℂ) / 2))) * (Real.sin (θ / 2) : ℂ),
        Complex.exp (Complex.I * (φ : ℂ) / 2) * (Real.cos (θ / 2) : ℂ)] := by
  unfold spinHalfRot3 spinHalfRot2 rotOf spinHalfOp3 spinHalfOp2 pauliZ pauliY
  ext i
  fin_cases i
  · -- case 0: up component (involves I² from σ_y)
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
       spinHalfDown, Matrix.smul_apply, Matrix.sub_apply]
    rw [show -(Complex.I * (φ : ℂ) / 2) = (-(↑φ / 2)) * Complex.I from by ring,
      Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, neg_mul]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination
      (Complex.sin (↑θ / 2)) *
        (Complex.cos (↑φ / 2) - Complex.I * Complex.sin (↑φ / 2)) * hI
  · -- case 1: down component (no I² terms)
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
       spinHalfDown, Matrix.smul_apply, Matrix.sub_apply]
    rw [show Complex.I * (φ : ℂ) / 2 = (↑φ / 2) * Complex.I from by ring,
      Complex.exp_mul_I]
    left
    push_cast; ring

/-! ## Problem 2.1.e: phase factor at θ = φ = π/2 -/

/-- Tasaki Problem 2.1.e: at `θ = φ = π/2` the coherent state
specializes to `e^{-iπ/4} cos(π/4) |ψ^↑⟩ + e^{iπ/4} sin(π/4) |ψ^↓⟩`. -/
theorem spinHalfRot3_half_pi_mul_spinHalfRot2_half_pi_mulVec_spinHalfUp :
    (spinHalfRot3 (Real.pi / 2) * spinHalfRot2 (Real.pi / 2)).mulVec spinHalfUp =
      ![Complex.exp (-(Complex.I * Real.pi / 4)) * (Real.cos (Real.pi / 4) : ℂ),
        Complex.exp (Complex.I * Real.pi / 4) * (Real.sin (Real.pi / 4) : ℂ)] := by
  have h := spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp (Real.pi / 2) (Real.pi / 2)
  convert h using 2 <;> push_cast <;> ring

/-! ## Vector inner product `Ŝ · v` (Tasaki eq (2.1.19))

For a 3-vector `v = (v₁, v₂, v₃)`, the inner product `Ŝ · v :=
v₁ Ŝ^(1) + v₂ Ŝ^(2) + v₃ Ŝ^(3)` is the spin operator projected onto
direction `v`. -/

/-- Vector inner product `Ŝ · v` for `S = 1/2`. -/
noncomputable def spinHalfDotVec (v : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  v 0 • spinHalfOp1 + v 1 • spinHalfOp2 + v 2 • spinHalfOp3

/-- `Ŝ · v` is Hermitian when `v` is real-valued (so `star v = v`). -/
theorem spinHalfDotVec_isHermitian (v : Fin 3 → ℂ)
    (hv : ∀ i, star (v i) = v i) :
    (spinHalfDotVec v).IsHermitian := by
  unfold spinHalfDotVec
  refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hv 0, spinHalfOp1_isHermitian]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hv 1, spinHalfOp2_isHermitian]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hv 2, spinHalfOp3_isHermitian]

/-- Same-axis rotation commutes with the spin operator along that axis. -/
theorem spinHalfRot3_commute_spinHalfOp3_smul (θ : ℝ) (v3 : ℂ) :
    spinHalfRot3 θ * (v3 • spinHalfOp3) =
      (v3 • spinHalfOp3) * spinHalfRot3 θ := by
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  exact (rotOf_comm_self spinHalfOp3 θ).symm

/-! ## Hadamard matrix (basis change between σ^x and σ^z) -/

/-- The Hadamard matrix `W = (1/√2)·!![1, 1; 1, -1]`. It satisfies
`W * W = 1` and `W * Ŝ^(1) * W = Ŝ^(3)`. These identities provide the
basis change that, with `Matrix.exp_units_conj`, would extend
Problem 2.1.b to axes 1 and 2. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 1; 1, -1]

/-- `(1/√2) * (1/√2) = 1/2` in `ℂ`; used to simplify Hadamard products. -/
private lemma sqrt2_inv_mul_sqrt2_inv :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; ring

/-- `W · W = 1` (the Hadamard matrix is its own inverse). -/
theorem hadamard_mul_self : hadamard * hadamard = 1 := by
  unfold hadamard
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqrt2_inv_mul_sqrt2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; norm_num) | simp

/-- `W · Ŝ^(3) · W = Ŝ^(1)` (the inverse direction of the Hadamard
basis change). -/
theorem hadamard_mul_spinHalfOp3_mul_hadamard :
    hadamard * spinHalfOp3 * hadamard = spinHalfOp1 := by
  unfold hadamard spinHalfOp1 spinHalfOp3 pauliX pauliZ
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [sqrt2_inv_mul_sqrt2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; ring) | simp

/-- `W · Ŝ^(1) · W = Ŝ^(3)` — the Hadamard takes the x-spin to the
z-spin (basis change). -/
theorem hadamard_mul_spinHalfOp1_mul_hadamard :
    hadamard * spinHalfOp1 * hadamard = spinHalfOp3 := by
  unfold hadamard spinHalfOp1 spinHalfOp3 pauliX pauliZ
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [sqrt2_inv_mul_sqrt2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; ring) | simp

/-- `Û^(1)_θ` is the Hadamard-conjugate of `Û^(3)_θ`. -/
theorem spinHalfRot1_eq_hadamard_conj (θ : ℝ) :
    spinHalfRot1 θ = hadamard * spinHalfRot3 θ * hadamard := by
  unfold spinHalfRot1 spinHalfRot3 rotOf
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
    mul_smul_comm, smul_mul_assoc, hadamard_mul_self,
    hadamard_mul_spinHalfOp3_mul_hadamard]

/-- Problem 2.1.b for axis 1: `Û^(1)_θ = exp(-iθ Ŝ^(1))`.
Derived from the axis-3 case via Hadamard conjugation
(`Matrix.exp_conj`). -/
theorem spinHalfRot1_eq_exp (θ : ℝ) :
    spinHalfRot1 θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • spinHalfOp1) := by
  rw [spinHalfRot1_eq_hadamard_conj, spinHalfRot3_eq_exp]
  have hU : IsUnit hadamard := IsUnit.of_mul_eq_one hadamard hadamard_mul_self
  have hWinv : hadamard⁻¹ = hadamard :=
    Matrix.inv_eq_left_inv hadamard_mul_self
  rw [show (-(Complex.I * (θ : ℂ))) • spinHalfOp1 =
      hadamard * ((-(Complex.I * (θ : ℂ))) • spinHalfOp3) * hadamard⁻¹ from by
    rw [hWinv, mul_smul_comm, smul_mul_assoc,
      hadamard_mul_spinHalfOp3_mul_hadamard]]
  rw [Matrix.exp_conj _ _ hU, hWinv]

/-! ## y-axis diagonalizer (basis change between σ^y and σ^z) -/

/-- The unitary `V = (1/√2)·!![1, 1; i, -i]` whose columns are the
`σ^y` eigenvectors. It satisfies `V · Ŝ^(3) · V† = Ŝ^(2)`. -/
noncomputable def yDiag : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 1; Complex.I, -Complex.I]

/-- Adjoint (= inverse) of `yDiag`. -/
noncomputable def yDiagAdj : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![1, -Complex.I; 1, Complex.I]

/-- `V · V† = 1`. -/
theorem yDiag_mul_yDiagAdj : yDiag * yDiagAdj = 1 := by
  unfold yDiag yDiagAdj
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt2_inv_mul_sqrt2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; ring) | simp

/-- `V† · V = 1`. -/
theorem yDiagAdj_mul_yDiag : yDiagAdj * yDiag = 1 := by
  unfold yDiag yDiagAdj
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt2_inv_mul_sqrt2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; ring) | simp

/-- `V · Ŝ^(3) · V† = Ŝ^(2)`. -/
theorem yDiag_mul_spinHalfOp3_mul_yDiagAdj :
    yDiag * spinHalfOp3 * yDiagAdj = spinHalfOp2 := by
  unfold yDiag yDiagAdj spinHalfOp3 spinHalfOp2 pauliZ pauliY
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [sqrt2_inv_mul_sqrt2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | (simp; ring) | simp

/-- `Û^(2)_θ = V · Û^(3)_θ · V†` (analog of `spinHalfRot1_eq_hadamard_conj`). -/
theorem spinHalfRot2_eq_yDiag_conj (θ : ℝ) :
    spinHalfRot2 θ = yDiag * spinHalfRot3 θ * yDiagAdj := by
  unfold spinHalfRot2 spinHalfRot3 rotOf
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
    mul_smul_comm, smul_mul_assoc, yDiag_mul_yDiagAdj,
    yDiag_mul_spinHalfOp3_mul_yDiagAdj]

/-- Problem 2.1.b for axis 2: `Û^(2)_θ = exp(-iθ Ŝ^(2))`. -/
theorem spinHalfRot2_eq_exp (θ : ℝ) :
    spinHalfRot2 θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • spinHalfOp2) := by
  rw [spinHalfRot2_eq_yDiag_conj, spinHalfRot3_eq_exp]
  have hU : IsUnit yDiag := IsUnit.of_mul_eq_one yDiagAdj yDiag_mul_yDiagAdj
  have hWinv : yDiag⁻¹ = yDiagAdj :=
    Matrix.inv_eq_left_inv yDiagAdj_mul_yDiag
  rw [show (-(Complex.I * (θ : ℂ))) • spinHalfOp2 =
      yDiag * ((-(Complex.I * (θ : ℂ))) • spinHalfOp3) * yDiag⁻¹ from by
    rw [hWinv, mul_smul_comm, smul_mul_assoc,
      yDiag_mul_spinHalfOp3_mul_yDiagAdj]]
  rw [Matrix.exp_conj _ _ hU, hWinv]


end LatticeSystem.Quantum
