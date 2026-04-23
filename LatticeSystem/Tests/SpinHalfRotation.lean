/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalfRotation
import LatticeSystem.Quantum.SpinHalfRotation.Conjugation

/-!
# Test coverage for Quantum/SpinHalfRotation (and `.Conjugation` extension)

A+C+G+D coverage for the spin-1/2 rotation operators
`spinHalfRot{1,2,3}`, group law, π / 2π values, exp-form,
coherent state, Hadamard, and y-axis diagonalizer (refactor plan
v4 §9 mapping table; refactor Phase 1 PR 7 #281; codex audit
follow-up Item 5 added the extension-module coverage).
-/

namespace LatticeSystem.Tests.SpinHalfRotation

open LatticeSystem.Quantum Matrix

/-! ## D. signature shims (zero / 2π / group law) -/

/-- `Û^(1)_0 = 1`. -/
example : spinHalfRot1 0 = 1 := spinHalfRot1_zero

/-- `Û^(2)_0 = 1`. -/
example : spinHalfRot2 0 = 1 := spinHalfRot2_zero

/-- `Û^(3)_0 = 1`. -/
example : spinHalfRot3 0 = 1 := spinHalfRot3_zero

/-- `Û^(1)_{2π} = -1` (Tasaki §2.1 (2.1.23) at half-odd-integer
spin). -/
example : spinHalfRot1 (2 * Real.pi) = -1 := spinHalfRot1_two_pi

/-- `Û^(2)_{2π} = -1`. -/
example : spinHalfRot2 (2 * Real.pi) = -1 := spinHalfRot2_two_pi

/-- `Û^(3)_{2π} = -1`. -/
example : spinHalfRot3 (2 * Real.pi) = -1 := spinHalfRot3_two_pi

/-- Group law: `Û^(1)_θ · Û^(1)_φ = Û^(1)_{θ+φ}`. -/
example (θ φ : ℝ) :
    spinHalfRot1 θ * spinHalfRot1 φ = spinHalfRot1 (θ + φ) :=
  spinHalfRot1_mul θ φ

/-- Group law for axis 2. -/
example (θ φ : ℝ) :
    spinHalfRot2 θ * spinHalfRot2 φ = spinHalfRot2 (θ + φ) :=
  spinHalfRot2_mul θ φ

/-- Group law for axis 3. -/
example (θ φ : ℝ) :
    spinHalfRot3 θ * spinHalfRot3 φ = spinHalfRot3 (θ + φ) :=
  spinHalfRot3_mul θ φ

/-- Unitarity: `Û^(1)_θ · (Û^(1)_θ)† = 1`. -/
example (θ : ℝ) :
    spinHalfRot1 θ * (spinHalfRot1 θ).conjTranspose = 1 :=
  spinHalfRot1_unitary θ

/-- Unitarity for axis 3. -/
example (θ : ℝ) :
    spinHalfRot3 θ * (spinHalfRot3 θ).conjTranspose = 1 :=
  spinHalfRot3_unitary θ

/-! ## D. π-rotation closed form -/

/-- `Û^(1)_π = -2i · Ŝ^(1)`. -/
example : spinHalfRot1 Real.pi = (-(2 * Complex.I)) • spinHalfOp1 :=
  spinHalfRot1_pi

/-- `Û^(2)_π = -2i · Ŝ^(2)`. -/
example : spinHalfRot2 Real.pi = (-(2 * Complex.I)) • spinHalfOp2 :=
  spinHalfRot2_pi

/-- `Û^(3)_π = -2i · Ŝ^(3)`. -/
example : spinHalfRot3 Real.pi = (-(2 * Complex.I)) • spinHalfOp3 :=
  spinHalfRot3_pi

/-! ## D. Conjugation extension (`SpinHalfRotation/Conjugation.lean`)

Codex audit Item 5: pin representative results from the
extension sub-file so the test file actually exercises the
content it imports. -/

/-- General-θ conjugation for axis 3 over axis 1 (Tasaki eq.
(2.1.16)). -/
example (θ : ℝ) :
    (spinHalfRot3 θ)ᴴ * spinHalfOp1 * spinHalfRot3 θ =
      (Real.cos θ : ℂ) • spinHalfOp1 - (Real.sin θ : ℂ) • spinHalfOp2 :=
  spinHalfRot3_conj_spinHalfOp1 θ

/-- Exp-form (Tasaki Problem 2.1.b) for axis 3. -/
example (θ : ℝ) :
    spinHalfRot3 θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • spinHalfOp3) :=
  spinHalfRot3_eq_exp θ

/-- Hadamard squares to identity. -/
example : hadamard * hadamard = 1 := hadamard_mul_self

/-- Hadamard conjugation: `H · Ŝ^(3) · H = Ŝ^(1)`. -/
example :
    hadamard * spinHalfOp3 * hadamard = spinHalfOp1 :=
  hadamard_mul_spinHalfOp3_mul_hadamard

/-- Vector inner product `Ŝ · v` on the canonical axis-3 vector
`(0, 0, 1)` recovers `Ŝ^(3)`. -/
example :
    spinHalfDotVec ![0, 0, 1] = spinHalfOp3 := by
  unfold spinHalfDotVec
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end LatticeSystem.Tests.SpinHalfRotation
