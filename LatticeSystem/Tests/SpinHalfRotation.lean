/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalfRotation

/-!
# Test coverage for Quantum/SpinHalfRotation

A+C+G+D coverage for the spin-1/2 rotation operators
`spinHalfRot{1,2,3}`, group law, π / 2π values, and the
exp-form (refactor plan v4 §9 mapping table; refactor Phase 1 PR 7,
#281).
-/

namespace LatticeSystem.Tests.SpinHalfRotation

open LatticeSystem.Quantum

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

end LatticeSystem.Tests.SpinHalfRotation
