/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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

end LatticeSystem.Quantum
