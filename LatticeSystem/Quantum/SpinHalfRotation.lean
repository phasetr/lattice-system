/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
`Û^(α)_θ · (Û^(α)_θ)† = 1` are deferred to a follow-up PR, since their
proofs require matrix algebra in the non-commutative ring
`Matrix (Fin 2) (Fin 2) ℂ` restricted to the commutative subring
`span_ℂ {1, Ŝ^(α)}` with relation `(Ŝ^(α))² = I/4`.
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
private noncomputable def rotOf (S : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
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

private lemma rotOf_zero (S : Matrix (Fin 2) (Fin 2) ℂ) : rotOf S 0 = 1 := by
  simp [rotOf]

/-- `Û^(1)_0 = 1`. -/
theorem spinHalfRot1_zero : spinHalfRot1 0 = 1 := rotOf_zero _

/-- `Û^(2)_0 = 1`. -/
theorem spinHalfRot2_zero : spinHalfRot2 0 = 1 := rotOf_zero _

/-- `Û^(3)_0 = 1`. -/
theorem spinHalfRot3_zero : spinHalfRot3 0 = 1 := rotOf_zero _

/-! ## Adjoint = rotation by the opposite angle -/

private lemma rotOf_adjoint {S : Matrix (Fin 2) (Fin 2) ℂ}
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

private lemma rotOf_two_pi (S : Matrix (Fin 2) (Fin 2) ℂ) :
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

private lemma rotOf_mul_rotOf {S : Matrix (Fin 2) (Fin 2) ℂ}
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

private lemma rotOf_mul_conjTranspose {S : Matrix (Fin 2) (Fin 2) ℂ}
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

end LatticeSystem.Quantum
