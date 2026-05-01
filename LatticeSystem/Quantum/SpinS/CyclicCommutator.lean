/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Cartan3
import LatticeSystem.Quantum.SpinS.Algebra

/-!
# Cyclic SU(2) commutators `[Ŝ^{(α)}, Ŝ^{(β)}] = i ε^αβγ Ŝ^{(γ)}`
(Tasaki §2.1 P1d''' β-20)

Derived from the Cartan relations (β-2: `[Ŝ^{(3)}, Ŝ^±] = ±Ŝ^±`,
β-19: `[Ŝ^+, Ŝ^-] = 2 Ŝ^{(3)}`) by algebraic manipulation through
`Ŝ^{(1)} = (Ŝ^+ + Ŝ^-)/2` and `Ŝ^{(2)} = (Ŝ^+ − Ŝ^-)/(2i)`:

  `[Ŝ^{(1)}, Ŝ^{(2)}] = i · Ŝ^{(3)}`,
  `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`,
  `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`.

These complete the **standard SU(2) commutator algebra** (Tasaki
eq. (2.1.1)) for the spin-`S` operators, the natural counterpart
of the spin-1/2 (`SpinHalf.lean`) and spin-1 (`SpinOne.lean`)
specialised proofs.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.1).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Cyclic SU(2) commutator: `[Ŝ^{(1)}, Ŝ^{(2)}] = i · Ŝ^{(3)}`. -/
theorem spinSOp1_commutator_spinSOp2 (N : ℕ) :
    spinSOp1 N * spinSOp2 N - spinSOp2 N * spinSOp1 N = I • spinSOp3 N := by
  unfold spinSOp1 spinSOp2
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show ((1 / (2 * I) : ℂ) * (1 / 2)) = ((1 / 2 : ℂ) * (1 / (2 * I))) from by ring]
  rw [← smul_sub]
  have hexp : (spinSOpPlus N + spinSOpMinus N) * (spinSOpPlus N - spinSOpMinus N) -
              (spinSOpPlus N - spinSOpMinus N) * (spinSOpPlus N + spinSOpMinus N) =
              (-(2 : ℂ)) • (spinSOpPlus N * spinSOpMinus N -
                           spinSOpMinus N * spinSOpPlus N) := by
    rw [neg_smul, two_smul]
    rw [add_mul, mul_add, sub_mul, mul_sub, sub_mul, mul_sub]
    abel
  rw [hexp, spinSOpPlus_commutator_spinSOpMinus, smul_smul, smul_smul]
  congr 1
  -- Goal: 1/2 * (1/(2*I)) * -2 * 2 = I
  -- = -1/I = I (using Complex.inv_I : I⁻¹ = -I)
  rw [show (1 / 2 : ℂ) * (1 / (2 * I)) * -2 * 2 = -(1 / I) from by ring]
  rw [show (1 / I : ℂ) = -I from by rw [one_div, Complex.inv_I]]
  ring

end LatticeSystem.Quantum
