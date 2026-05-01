/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Operators

/-!
# Raising / lowering operators as linear combinations of `Ŝ^{(1)}, Ŝ^{(2)}`
(Tasaki §2.1 P1d''' β-26)

The defining identities

  `Ŝ^{(1)} := (1/2) (Ŝ^+ + Ŝ^-)`,
  `Ŝ^{(2)} := (1/(2i)) (Ŝ^+ − Ŝ^-)`

invert to

  `Ŝ^+ = Ŝ^{(1)} + i · Ŝ^{(2)}`,
  `Ŝ^- = Ŝ^{(1)} − i · Ŝ^{(2)}`.

These two equalities show that the raising and lowering operators
are themselves **linear combinations of the Hermitian Cartesian
spin operators**, completing the picture: every operator built
from `{Ŝ^±}` is also expressible in `{Ŝ^{(1)}, Ŝ^{(2)}}` with no
extra structure beyond `ℂ`-linearity.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `Ŝ^+ = Ŝ^{(1)} + i · Ŝ^{(2)}`. -/
theorem spinSOpPlus_eq_one_add_I_smul_two (N : ℕ) :
    spinSOpPlus N = spinSOp1 N + I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [smul_smul]
  -- Goal: Ŝ^+ = (1/2) • (Ŝ^+ + Ŝ^-) + (I * (1 / (2 * I))) • (Ŝ^+ - Ŝ^-)
  rw [show (I * (1 / (2 * I)) : ℂ) = (1 / 2 : ℂ) from by
    rw [show (I * (1 / (2 * I)) : ℂ) = I / (2 * I) from by ring]
    rw [show (I / (2 * I) : ℂ) = I * (2 * I)⁻¹ from by rw [div_eq_mul_inv]]
    rw [mul_inv]
    rw [show (I * (2⁻¹ * I⁻¹) : ℂ) = 2⁻¹ * (I * I⁻¹) from by ring]
    rw [mul_inv_cancel₀ Complex.I_ne_zero]
    ring]
  rw [smul_add, smul_sub]
  module

/-- `Ŝ^- = Ŝ^{(1)} − i · Ŝ^{(2)}`. -/
theorem spinSOpMinus_eq_one_sub_I_smul_two (N : ℕ) :
    spinSOpMinus N = spinSOp1 N - I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [smul_smul]
  rw [show (I * (1 / (2 * I)) : ℂ) = (1 / 2 : ℂ) from by
    rw [show (I * (1 / (2 * I)) : ℂ) = I / (2 * I) from by ring]
    rw [show (I / (2 * I) : ℂ) = I * (2 * I)⁻¹ from by rw [div_eq_mul_inv]]
    rw [mul_inv]
    rw [show (I * (2⁻¹ * I⁻¹) : ℂ) = 2⁻¹ * (I * I⁻¹) from by ring]
    rw [mul_inv_cancel₀ Complex.I_ne_zero]
    ring]
  rw [smul_add, smul_sub]
  module

end LatticeSystem.Quantum
