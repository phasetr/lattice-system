/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.SpinHalfBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Spin-1/2 rotation operators via the closed form

Formalizes the closed-form rotation operator for `S = 1/2` following
Tasaki *Physics and Mathematics of Quantum Many-Body Systems*, §2.1,
eq. (2.1.26) on p. 17:

```
Û^(α)_θ := cos(θ/2) · 1 - 2i · sin(θ/2) · Ŝ^(α).
```

For `S = 1/2` this is equivalent to the matrix exponential
`exp(-iθ Ŝ^(α))` because `(Ŝ^(α))² = I/4`; we take the closed form as
our definition here, deferring the equivalence with the matrix
exponential to future work.

We prove:

* `spinHalfRot1/2/3_zero`: identity at `θ = 0`.
* `spinHalfRot1/2/3_adjoint`: `(Û^(α)_θ)† = Û^(α)_{-θ}` — Tasaki p. 15
  ("We also have `(Û^(α)_θ)† = Û^(α)_{-θ}` by definition").
* `spinHalfRot1/2/3_two_pi`: the hallmark `S = 1/2` identity
  `Û^(α)_{2π} = -1` (Tasaki eq. (2.1.23), p. 16).

The group law `Û^(α)_θ · Û^(α)_φ = Û^(α)_{θ+φ}` and unitarity
`Û^(α)_θ · (Û^(α)_θ)† = 1` are formalised here as
`spinHalfRot{1,2,3}_mul` and `spinHalfRot{1,2,3}_unitary`
respectively. The matrix-exponential equivalence
`Û^(α)_θ = exp(-iθ Ŝ^(α))` (Tasaki Problem 2.1.b) is in the
extension sub-file `SpinHalfRotation/Conjugation.lean` as
`spinHalfRot{1,2,3}_eq_exp`.

Sub-files extending this module (Phase 2 PR 22 split, plan v4
§3.1):

| sub-file | content |
|---|---|
| `SpinHalfRotation/Conjugation.lean` | general-θ conjugation (Tasaki |
|                                     | eq. (2.1.16)), same-axis invariance |
|                                     | (eq. (2.1.15)), π/2 conjugation, exp |
|                                     | form (Problem 2.1.b), coherent state |
|                                     | (Problem 2.1.d), Problem 2.1.e, vector |
|                                     | inner product `Ŝ · v`, Hadamard, |
|                                     | y-axis diagonalizer |

Downstream code that wants the conjugation / coherent-state /
exp-form machinery should import
`Quantum.SpinHalfRotation.Conjugation` directly (this file is
content + extensions, not a façade).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Internal generic rotation

The three `spinHalfRotα` functions share a common structure, so we
factor through a private helper `rotOf` parameterised by an arbitrary
matrix `S : Matrix (Fin 2) (Fin 2) ℂ`. Each public `spinHalfRotα`
instantiates `rotOf` at `spinHalfOpα`.
-/

/-- Generic rotation builder: `cos(θ/2) · 1 - 2i · sin(θ/2) · S`. -/
noncomputable def rotOf (S : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (θ / 2) : ℂ) • 1 - (2 * I * (Real.sin (θ / 2) : ℂ)) • S

/-! ## Definitions -/

/-- Spin-1/2 rotation about axis 1: `Û^(1)_θ`. -/
noncomputable def spinHalfRot1 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotOf spinHalfOp1 θ

/-- Spin-1/2 rotation about axis 2: `Û^(2)_θ`. -/
noncomputable def spinHalfRot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotOf spinHalfOp2 θ

/-- Spin-1/2 rotation about axis 3: `Û^(3)_θ`. -/
noncomputable def spinHalfRot3 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotOf spinHalfOp3 θ

/-! ## Value at `θ = 0` -/

/-- `rotOf S 0 = 1`: the generic rotation is the identity at angle zero. -/
lemma rotOf_zero (S : Matrix (Fin 2) (Fin 2) ℂ) : rotOf S 0 = 1 := by
  simp [rotOf]

/-- `Û^(1)_0 = 1`. -/
theorem spinHalfRot1_zero : spinHalfRot1 0 = 1 := rotOf_zero _

/-- `Û^(2)_0 = 1`. -/
theorem spinHalfRot2_zero : spinHalfRot2 0 = 1 := rotOf_zero _

/-- `Û^(3)_0 = 1`. -/
theorem spinHalfRot3_zero : spinHalfRot3 0 = 1 := rotOf_zero _

/-! ## Adjoint = rotation by the opposite angle -/

/-- `(rotOf S θ)ᴴ = rotOf S (-θ)` when `S` is Hermitian. -/
lemma rotOf_adjoint {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S.IsHermitian) (θ : ℝ) :
    (rotOf S θ)ᴴ = rotOf S (-θ) := by
  unfold rotOf
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hS]
  congr 1
  · -- `star (cos(θ/2) : ℂ) • 1 = (cos(-θ/2) : ℂ) • 1`:
    -- `star` of a real-valued complex is itself, and cos is even.
    congr 1
    rw [show (-θ) / 2 = -(θ / 2) from by ring, Real.cos_neg]
    exact Complex.conj_ofReal _
  · -- `star (2 * I * sin(θ/2)) • S = (2 * I * sin(-θ/2)) • S`:
    -- LHS simplifies to `-2 * I * sin(θ/2)` via `star I = -I` and
    -- `star (sin θ : ℂ) = sin θ`. RHS equals `-2 * I * sin(θ/2)` via
    -- `sin(-x) = -sin(x)`.
    congr 1
    rw [show (-θ) / 2 = -(θ / 2) from by ring, Real.sin_neg,
      Complex.ofReal_neg]
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    have hstar : star (2 * I * ((Real.sin (θ / 2) : ℝ) : ℂ))
        = -(2 * I * ((Real.sin (θ / 2) : ℝ) : ℂ)) := by
      change (starRingEnd ℂ) _ = _
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, h2]
      ring
    rw [hstar]
    ring

/-- `(Û^(1)_θ)† = Û^(1)_{-θ}`. -/
theorem spinHalfRot1_adjoint (θ : ℝ) :
    (spinHalfRot1 θ)ᴴ = spinHalfRot1 (-θ) :=
  rotOf_adjoint spinHalfOp1_isHermitian θ

/-- `(Û^(2)_θ)† = Û^(2)_{-θ}`. -/
theorem spinHalfRot2_adjoint (θ : ℝ) :
    (spinHalfRot2 θ)ᴴ = spinHalfRot2 (-θ) :=
  rotOf_adjoint spinHalfOp2_isHermitian θ

/-- `(Û^(3)_θ)† = Û^(3)_{-θ}`. -/
theorem spinHalfRot3_adjoint (θ : ℝ) :
    (spinHalfRot3 θ)ᴴ = spinHalfRot3 (-θ) :=
  rotOf_adjoint spinHalfOp3_isHermitian θ

/-! ## Rotation by `2π` (Tasaki eq 2.1.23 for S = 1/2) -/

/-- `rotOf S (2π) = -1`: the 2π rotation gives `-1` for any spin operator `S`. -/
lemma rotOf_two_pi (S : Matrix (Fin 2) (Fin 2) ℂ) :
    rotOf S (2 * Real.pi) = -1 := by
  unfold rotOf
  -- cos(π) = -1, sin(π) = 0
  rw [show (2 * Real.pi) / 2 = Real.pi from by ring]
  rw [Real.cos_pi, Real.sin_pi]
  push_cast
  simp

/-- `Û^(1)_{2π} = -1` for S = 1/2 (Tasaki eq 2.1.23, p. 16). -/
theorem spinHalfRot1_two_pi : spinHalfRot1 (2 * Real.pi) = -1 :=
  rotOf_two_pi _

/-- `Û^(2)_{2π} = -1` for S = 1/2. -/
theorem spinHalfRot2_two_pi : spinHalfRot2 (2 * Real.pi) = -1 :=
  rotOf_two_pi _

/-- `Û^(3)_{2π} = -1` for S = 1/2. -/
theorem spinHalfRot3_two_pi : spinHalfRot3 (2 * Real.pi) = -1 :=
  rotOf_two_pi _

/-! ## Helper lemma for matrix algebra in `span_ℂ {1, S}` -/

/-- Expansion lemma: if `S * S = k · 1` then
`(a • 1 - b • S) * (c • 1 - d • S) = (a*c + b*d*k) • 1 - (a*d + b*c) • S`.
This is the key identity that lets us reduce products of rotation-style
matrices to linear combinations of `1` and `S`. -/
private lemma rot_mul_helper {S : Matrix (Fin 2) (Fin 2) ℂ} {k : ℂ}
    (hS : S * S = k • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (a b c d : ℂ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℂ) - b • S) * (c • 1 - d • S)
      = (a * c + b * d * k) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (a * d + b * c) • S := by
  rw [sub_mul, mul_sub, mul_sub,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hS,
      smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  module

/-! ## Group law `Û^(α)_θ · Û^(α)_φ = Û^(α)_{θ+φ}` -/

/-- Group law for `rotOf`: product of two generic rotations equals
the rotation by the sum of angles, when `S * S = (1/4) · 1`. -/
lemma rotOf_mul_rotOf {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS_sq : S * S = (1 / 4 : ℂ) • 1) (θ φ : ℝ) :
    rotOf S θ * rotOf S φ = rotOf S (θ + φ) := by
  unfold rotOf
  rw [rot_mul_helper hS_sq,
    show (θ + φ) / 2 = θ / 2 + φ / 2 from by ring,
    Real.cos_add, Real.sin_add]
  push_cast
  congr 1
  · -- `1`-coefficient match: uses `I^2 = -1`.
    congr 1
    linear_combination (Complex.sin ((θ : ℂ) / 2) * Complex.sin ((φ : ℂ) / 2)) * Complex.I_sq
  · -- `S`-coefficient match: pure ring identity, no `I^2` involved.
    congr 1
    ring

/-- `Û^(1)_θ · Û^(1)_φ = Û^(1)_{θ+φ}`. -/
theorem spinHalfRot1_mul (θ φ : ℝ) :
    spinHalfRot1 θ * spinHalfRot1 φ = spinHalfRot1 (θ + φ) :=
  rotOf_mul_rotOf spinHalfOp1_mul_self θ φ

/-- `Û^(2)_θ · Û^(2)_φ = Û^(2)_{θ+φ}`. -/
theorem spinHalfRot2_mul (θ φ : ℝ) :
    spinHalfRot2 θ * spinHalfRot2 φ = spinHalfRot2 (θ + φ) :=
  rotOf_mul_rotOf spinHalfOp2_mul_self θ φ

/-- `Û^(3)_θ · Û^(3)_φ = Û^(3)_{θ+φ}`. -/
theorem spinHalfRot3_mul (θ φ : ℝ) :
    spinHalfRot3 θ * spinHalfRot3 φ = spinHalfRot3 (θ + φ) :=
  rotOf_mul_rotOf spinHalfOp3_mul_self θ φ

/-! ## Unitarity `Û^(α)_θ · (Û^(α)_θ)† = 1` -/

/-- `rotOf S θ * (rotOf S θ)ᴴ = 1`: unitarity of the generic rotation. -/
lemma rotOf_mul_conjTranspose {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S.IsHermitian) (hS_sq : S * S = (1 / 4 : ℂ) • 1) (θ : ℝ) :
    rotOf S θ * (rotOf S θ)ᴴ = 1 := by
  rw [rotOf_adjoint hS, rotOf_mul_rotOf hS_sq, add_neg_cancel]
  exact rotOf_zero S

/-- `Û^(1)_θ · (Û^(1)_θ)† = 1`. -/
theorem spinHalfRot1_unitary (θ : ℝ) :
    spinHalfRot1 θ * (spinHalfRot1 θ)ᴴ = 1 :=
  rotOf_mul_conjTranspose spinHalfOp1_isHermitian spinHalfOp1_mul_self θ

/-- `Û^(2)_θ · (Û^(2)_θ)† = 1`. -/
theorem spinHalfRot2_unitary (θ : ℝ) :
    spinHalfRot2 θ * (spinHalfRot2 θ)ᴴ = 1 :=
  rotOf_mul_conjTranspose spinHalfOp2_isHermitian spinHalfOp2_mul_self θ

/-- `Û^(3)_θ · (Û^(3)_θ)† = 1`. -/
theorem spinHalfRot3_unitary (θ : ℝ) :
    spinHalfRot3 θ * (spinHalfRot3 θ)ᴴ = 1 :=
  rotOf_mul_conjTranspose spinHalfOp3_isHermitian spinHalfOp3_mul_self θ

/-! ## `Û^(α)_θ` has determinant 1 (preparation for SU2.lean)

The closed-form rotation matrix has
`det = cos²(θ/2) + sin²(θ/2) = 1` (Pythagorean identity, complex form).
This makes `Û^(α)_θ` an element of `SU(2)` (the special unitary group),
not just `U(2)`. -/

/-- `det Û^(1)_θ = cos²(θ/2) + sin²(θ/2) = 1`. -/
theorem spinHalfRot1_det_eq_one (θ : ℝ) : (spinHalfRot1 θ).det = 1 := by
  unfold spinHalfRot1 rotOf spinHalfOp1
  rw [Matrix.det_fin_two]
  have hcs : Complex.cos ((θ : ℂ) / 2) ^ 2 + Complex.sin ((θ : ℂ) / 2) ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq _
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  simp [pauliX, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_div]
  linear_combination hcs - (Complex.sin ((θ : ℂ) / 2)) ^ 2 * hI

/-- `det Û^(2)_θ = 1`. The pauliY case has an extra `I^4` term in the
expansion that we cancel using `(I^2 - 1) · sin² · hI`. -/
theorem spinHalfRot2_det_eq_one (θ : ℝ) : (spinHalfRot2 θ).det = 1 := by
  unfold spinHalfRot2 rotOf spinHalfOp2
  rw [Matrix.det_fin_two]
  have hcs : Complex.cos ((θ : ℂ) / 2) ^ 2 + Complex.sin ((θ : ℂ) / 2) ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq _
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  simp [pauliY, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_div]
  linear_combination hcs +
    (Complex.sin ((θ : ℂ) / 2)) ^ 2 * (Complex.I ^ 2 - 1) * hI

/-- `det Û^(3)_θ = 1`. -/
theorem spinHalfRot3_det_eq_one (θ : ℝ) : (spinHalfRot3 θ).det = 1 := by
  unfold spinHalfRot3 rotOf spinHalfOp3
  rw [Matrix.det_fin_two]
  have hcs : Complex.cos ((θ : ℂ) / 2) ^ 2 + Complex.sin ((θ : ℂ) / 2) ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq _
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  simp [pauliZ, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_div]
  linear_combination hcs - (Complex.sin ((θ : ℂ) / 2)) ^ 2 * hI

/-! ## `Û^(α)_π`: the `π` rotation as `-2i · Ŝ^(α)` (Tasaki eq 2.1.26 at θ=π) -/

/-- `rotOf S π = (-2i) • S`: the π-rotation is a pure imaginary multiple of `S`. -/
lemma rotOf_pi (S : Matrix (Fin 2) (Fin 2) ℂ) :
    rotOf S Real.pi = (-(2 * I)) • S := by
  unfold rotOf
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- `Û^(1)_π = -2i · Ŝ^(1)`. -/
theorem spinHalfRot1_pi : spinHalfRot1 Real.pi = (-(2 * I)) • spinHalfOp1 :=
  rotOf_pi _

/-- `Û^(2)_π = -2i · Ŝ^(2)`. -/
theorem spinHalfRot2_pi : spinHalfRot2 Real.pi = (-(2 * I)) • spinHalfOp2 :=
  rotOf_pi _

/-- `Û^(3)_π = -2i · Ŝ^(3)`. -/
theorem spinHalfRot3_pi : spinHalfRot3 Real.pi = (-(2 * I)) • spinHalfOp3 :=
  rotOf_pi _

/-! ## `(Û^(α)_π)² = -1` -/

/-- `(Û^(1)_π)² = -1` (from group law and `Û^(1)_{2π} = -1`). -/
theorem spinHalfRot1_pi_sq :
    spinHalfRot1 Real.pi * spinHalfRot1 Real.pi = -1 := by
  rw [spinHalfRot1_mul, show Real.pi + Real.pi = 2 * Real.pi from by ring,
    spinHalfRot1_two_pi]

/-- `(Û^(2)_π)² = -1`. -/
theorem spinHalfRot2_pi_sq :
    spinHalfRot2 Real.pi * spinHalfRot2 Real.pi = -1 := by
  rw [spinHalfRot2_mul, show Real.pi + Real.pi = 2 * Real.pi from by ring,
    spinHalfRot2_two_pi]

/-- `(Û^(3)_π)² = -1`. -/
theorem spinHalfRot3_pi_sq :
    spinHalfRot3 Real.pi * spinHalfRot3 Real.pi = -1 := by
  rw [spinHalfRot3_mul, show Real.pi + Real.pi = 2 * Real.pi from by ring,
    spinHalfRot3_two_pi]

/-! ## π-rotation anticommutation at distinct axes (Tasaki eq 2.1.25, S = 1/2) -/

/-- `Û^(1)_π · Û^(2)_π + Û^(2)_π · Û^(1)_π = 0`. -/
theorem spinHalfRot1_pi_anticomm_spinHalfRot2_pi :
    spinHalfRot1 Real.pi * spinHalfRot2 Real.pi
      + spinHalfRot2 Real.pi * spinHalfRot1 Real.pi = 0 := by
  rw [spinHalfRot1_pi, spinHalfRot2_pi,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_add,
    spinHalfOp1_anticomm_spinHalfOp2, smul_zero]

/-- `Û^(2)_π · Û^(3)_π + Û^(3)_π · Û^(2)_π = 0`. -/
theorem spinHalfRot2_pi_anticomm_spinHalfRot3_pi :
    spinHalfRot2 Real.pi * spinHalfRot3 Real.pi
      + spinHalfRot3 Real.pi * spinHalfRot2 Real.pi = 0 := by
  rw [spinHalfRot2_pi, spinHalfRot3_pi,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_add,
    spinHalfOp2_anticomm_spinHalfOp3, smul_zero]

/-- `Û^(3)_π · Û^(1)_π + Û^(1)_π · Û^(3)_π = 0`. -/
theorem spinHalfRot3_pi_anticomm_spinHalfRot1_pi :
    spinHalfRot3 Real.pi * spinHalfRot1 Real.pi
      + spinHalfRot1 Real.pi * spinHalfRot3 Real.pi = 0 := by
  rw [spinHalfRot3_pi, spinHalfRot1_pi,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_add,
    spinHalfOp3_anticomm_spinHalfOp1, smul_zero]

/-! ## `(Û^(α)_π)† = 2i · Ŝ^(α)` -/

/-- `rotOf S (-π) = (2i) • S`: the negative-π rotation is the conjugate of the π-rotation. -/
lemma rotOf_neg_pi (S : Matrix (Fin 2) (Fin 2) ℂ) :
    rotOf S (-Real.pi) = (2 * I) • S := by
  unfold rotOf
  rw [show -Real.pi / 2 = -(Real.pi / 2) from by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(rotOf S π)ᴴ = (2i) • S` when `S` is Hermitian. -/
lemma rotOf_pi_conjTranspose {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S.IsHermitian) :
    (rotOf S Real.pi)ᴴ = (2 * I) • S := by
  rw [rotOf_adjoint hS, rotOf_neg_pi]

/-- `(Û^(1)_π)† = 2i · Ŝ^(1)`. -/
theorem spinHalfRot1_pi_conjTranspose :
    (spinHalfRot1 Real.pi)ᴴ = (2 * I) • spinHalfOp1 :=
  rotOf_pi_conjTranspose spinHalfOp1_isHermitian

/-- `(Û^(2)_π)† = 2i · Ŝ^(2)`. -/
theorem spinHalfRot2_pi_conjTranspose :
    (spinHalfRot2 Real.pi)ᴴ = (2 * I) • spinHalfOp2 :=
  rotOf_pi_conjTranspose spinHalfOp2_isHermitian

/-- `(Û^(3)_π)† = 2i · Ŝ^(3)`. -/
theorem spinHalfRot3_pi_conjTranspose :
    (spinHalfRot3 Real.pi)ᴴ = (2 * I) • spinHalfOp3 :=
  rotOf_pi_conjTranspose spinHalfOp3_isHermitian

/-! ## π-rotation products (Tasaki eq 2.1.29, S = 1/2) -/

/-- `Û^(1)_π · Û^(2)_π = Û^(3)_π`. -/
theorem spinHalfRot1_pi_mul_spinHalfRot2_pi :
    spinHalfRot1 Real.pi * spinHalfRot2 Real.pi = spinHalfRot3 Real.pi := by
  rw [spinHalfRot1_pi, spinHalfRot2_pi, spinHalfRot3_pi,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp1_mul_spinHalfOp2, smul_smul]
  congr 1
  linear_combination (2 * I) * Complex.I_sq

/-- `Û^(2)_π · Û^(3)_π = Û^(1)_π`. -/
theorem spinHalfRot2_pi_mul_spinHalfRot3_pi :
    spinHalfRot2 Real.pi * spinHalfRot3 Real.pi = spinHalfRot1 Real.pi := by
  rw [spinHalfRot2_pi, spinHalfRot3_pi, spinHalfRot1_pi,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp2_mul_spinHalfOp3, smul_smul]
  congr 1
  linear_combination (2 * I) * Complex.I_sq

/-- `Û^(3)_π · Û^(1)_π = Û^(2)_π`. -/
theorem spinHalfRot3_pi_mul_spinHalfRot1_pi :
    spinHalfRot3 Real.pi * spinHalfRot1 Real.pi = spinHalfRot2 Real.pi := by
  rw [spinHalfRot3_pi, spinHalfRot1_pi, spinHalfRot2_pi,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp3_mul_spinHalfOp1, smul_smul]
  congr 1
  linear_combination (2 * I) * Complex.I_sq

/-! ## Same-axis coordinate transformation at `θ = π`

Tasaki eq. (2.1.15) specializes to `Ŝ^(α)` being invariant under
conjugation by `Û^(α)_θ` (the axis of rotation is fixed). At `θ = π`
the statement is `(Û^(α)_π)† · Ŝ^(α) · Û^(α)_π = Ŝ^(α)`.
-/

/-- `(Û^(1)_π)† · Ŝ^(1) · Û^(1)_π = Ŝ^(1)`. -/
theorem spinHalfRot1_pi_conj_spinHalfOp1 :
    (spinHalfRot1 Real.pi)ᴴ * spinHalfOp1 * spinHalfRot1 Real.pi = spinHalfOp1 := by
  rw [spinHalfRot1_pi_conjTranspose, spinHalfRot1_pi,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp1_mul_self, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  conv_rhs => rw [show (spinHalfOp1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (1 : ℂ) • spinHalfOp1 from (one_smul _ _).symm]
  congr 1
  linear_combination -Complex.I_sq

/-- `(Û^(2)_π)† · Ŝ^(2) · Û^(2)_π = Ŝ^(2)`. -/
theorem spinHalfRot2_pi_conj_spinHalfOp2 :
    (spinHalfRot2 Real.pi)ᴴ * spinHalfOp2 * spinHalfRot2 Real.pi = spinHalfOp2 := by
  rw [spinHalfRot2_pi_conjTranspose, spinHalfRot2_pi,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp2_mul_self, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  conv_rhs => rw [show (spinHalfOp2 : Matrix (Fin 2) (Fin 2) ℂ)
      = (1 : ℂ) • spinHalfOp2 from (one_smul _ _).symm]
  congr 1
  linear_combination -Complex.I_sq

/-- `(Û^(3)_π)† · Ŝ^(3) · Û^(3)_π = Ŝ^(3)`. -/
theorem spinHalfRot3_pi_conj_spinHalfOp3 :
    (spinHalfRot3 Real.pi)ᴴ * spinHalfOp3 * spinHalfRot3 Real.pi = spinHalfOp3 := by
  rw [spinHalfRot3_pi_conjTranspose, spinHalfRot3_pi,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp3_mul_self, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  conv_rhs => rw [show (spinHalfOp3 : Matrix (Fin 2) (Fin 2) ℂ)
      = (1 : ℂ) • spinHalfOp3 from (one_smul _ _).symm]
  congr 1
  linear_combination -Complex.I_sq

/-! ## Flip coordinate transformation at `θ = π` for distinct axes

Tasaki eq. (2.1.21) specializes at `θ = π` to
`(Û^(α)_π)† · Ŝ^(β) · Û^(α)_π = -Ŝ^(β)` for `α ≠ β`. For the S = 1/2
representation this follows from `Ŝ^(α) · Ŝ^(β) · Ŝ^(α) = -(1/4) · Ŝ^(β)`,
itself a corollary of the single-site anticommutation relations.
-/

/-- For anticommuting `Sα` and `Sβ` with `Sα * Sα = (1/4) · 1`, the triple
product collapses: `Sα · Sβ · Sα = -(1/4) · Sβ`. -/
lemma spinHalfOp_triple_of_anticomm
    {Sα Sβ : Matrix (Fin 2) (Fin 2) ℂ}
    (hα_sq : Sα * Sα = (1 / 4 : ℂ) • 1)
    (hanti : Sα * Sβ + Sβ * Sα = 0) :
    Sα * Sβ * Sα = (-(1 / 4 : ℂ)) • Sβ := by
  have hSαSβ : Sα * Sβ = -(Sβ * Sα) := by
    rw [eq_neg_iff_add_eq_zero]; exact hanti
  calc Sα * Sβ * Sα
      = (-(Sβ * Sα)) * Sα := by rw [hSαSβ]
    _ = -(Sβ * Sα * Sα) := by rw [neg_mul]
    _ = -(Sβ * (Sα * Sα)) := by rw [mul_assoc]
    _ = -(Sβ * ((1 / 4 : ℂ) • 1)) := by rw [hα_sq]
    _ = -((1 / 4 : ℂ) • (Sβ * 1)) := by rw [Matrix.mul_smul]
    _ = -((1 / 4 : ℂ) • Sβ) := by rw [Matrix.mul_one]
    _ = (-(1 / 4 : ℂ)) • Sβ := by rw [neg_smul]

/-- Symmetry of anticommutation: `A * B + B * A = 0` implies `B * A + A * B = 0`. -/
lemma anticomm_swap {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (h : A * B + B * A = 0) : B * A + A * B = 0 := by
  rw [add_comm]; exact h

/-- `(rotOf Sα π)ᴴ * Sβ * rotOf Sα π = -Sβ` when `Sα` and `Sβ` anticommute. -/
lemma rotOf_pi_conj_of_ne {Sα Sβ : Matrix (Fin 2) (Fin 2) ℂ}
    (hα : Sα.IsHermitian) (hα_sq : Sα * Sα = (1 / 4 : ℂ) • 1)
    (hanti : Sα * Sβ + Sβ * Sα = 0) :
    (rotOf Sα Real.pi)ᴴ * Sβ * rotOf Sα Real.pi = -Sβ := by
  rw [rotOf_pi_conjTranspose hα, rotOf_pi,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinHalfOp_triple_of_anticomm hα_sq hanti, smul_smul]
  conv_rhs => rw [show -Sβ = ((-1 : ℂ)) • Sβ from (neg_one_smul _ _).symm]
  congr 1
  linear_combination Complex.I_sq

/-- `(Û^(1)_π)† · Ŝ^(2) · Û^(1)_π = -Ŝ^(2)`. -/
theorem spinHalfRot1_pi_conj_spinHalfOp2 :
    (spinHalfRot1 Real.pi)ᴴ * spinHalfOp2 * spinHalfRot1 Real.pi = -spinHalfOp2 :=
  rotOf_pi_conj_of_ne spinHalfOp1_isHermitian spinHalfOp1_mul_self
    spinHalfOp1_anticomm_spinHalfOp2

/-- `(Û^(1)_π)† · Ŝ^(3) · Û^(1)_π = -Ŝ^(3)`. -/
theorem spinHalfRot1_pi_conj_spinHalfOp3 :
    (spinHalfRot1 Real.pi)ᴴ * spinHalfOp3 * spinHalfRot1 Real.pi = -spinHalfOp3 :=
  rotOf_pi_conj_of_ne spinHalfOp1_isHermitian spinHalfOp1_mul_self
    (anticomm_swap spinHalfOp3_anticomm_spinHalfOp1)

/-- `(Û^(2)_π)† · Ŝ^(1) · Û^(2)_π = -Ŝ^(1)`. -/
theorem spinHalfRot2_pi_conj_spinHalfOp1 :
    (spinHalfRot2 Real.pi)ᴴ * spinHalfOp1 * spinHalfRot2 Real.pi = -spinHalfOp1 :=
  rotOf_pi_conj_of_ne spinHalfOp2_isHermitian spinHalfOp2_mul_self
    (anticomm_swap spinHalfOp1_anticomm_spinHalfOp2)

/-- `(Û^(2)_π)† · Ŝ^(3) · Û^(2)_π = -Ŝ^(3)`. -/
theorem spinHalfRot2_pi_conj_spinHalfOp3 :
    (spinHalfRot2 Real.pi)ᴴ * spinHalfOp3 * spinHalfRot2 Real.pi = -spinHalfOp3 :=
  rotOf_pi_conj_of_ne spinHalfOp2_isHermitian spinHalfOp2_mul_self
    spinHalfOp2_anticomm_spinHalfOp3

/-- `(Û^(3)_π)† · Ŝ^(1) · Û^(3)_π = -Ŝ^(1)`. -/
theorem spinHalfRot3_pi_conj_spinHalfOp1 :
    (spinHalfRot3 Real.pi)ᴴ * spinHalfOp1 * spinHalfRot3 Real.pi = -spinHalfOp1 :=
  rotOf_pi_conj_of_ne spinHalfOp3_isHermitian spinHalfOp3_mul_self
    spinHalfOp3_anticomm_spinHalfOp1

/-- `(Û^(3)_π)† · Ŝ^(2) · Û^(3)_π = -Ŝ^(2)`. -/
theorem spinHalfRot3_pi_conj_spinHalfOp2 :
    (spinHalfRot3 Real.pi)ᴴ * spinHalfOp2 * spinHalfRot3 Real.pi = -spinHalfOp2 :=
  rotOf_pi_conj_of_ne spinHalfOp3_isHermitian spinHalfOp3_mul_self
    (anticomm_swap spinHalfOp2_anticomm_spinHalfOp3)

end LatticeSystem.Quantum
