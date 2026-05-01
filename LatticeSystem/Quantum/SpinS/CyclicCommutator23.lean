/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.CyclicCommutator

/-!
# Second cyclic SU(2) commutator `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`
(Tasaki §2.1 P1d''' β-21)

The second of the three cyclic SU(2) commutators for the spin-`S`
operators on `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ`. Derived from
the Cartan relations β-2:

* `Ŝ^{(3)} Ŝ^+ - Ŝ^+ Ŝ^{(3)} = Ŝ^+`,
* `Ŝ^{(3)} Ŝ^- - Ŝ^- Ŝ^{(3)} = -Ŝ^-`,

via the expansion `Ŝ^{(2)} = (Ŝ^+ - Ŝ^-)/(2i)` together with the
identity `Ŝ^{(1)} = (Ŝ^+ + Ŝ^-)/2`:

  `[Ŝ^{(2)}, Ŝ^{(3)}] = (1/(2i)) (-Ŝ^+ - Ŝ^-) = (-1/i) Ŝ^{(1)} = i Ŝ^{(1)}`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.1).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Cyclic SU(2) commutator: `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`. -/
theorem spinSOp2_commutator_spinSOp3 (N : ℕ) :
    spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N = I • spinSOp1 N := by
  unfold spinSOp2 spinSOp1
  rw [Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_sub]
  -- Goal: (1/(2*I)) • ((Ŝ^+ - Ŝ^-) * Ŝ^(3) - Ŝ^(3) * (Ŝ^+ - Ŝ^-)) = I • ((1/2) • (Ŝ^+ + Ŝ^-))
  have hexp : (spinSOpPlus N - spinSOpMinus N) * spinSOp3 N -
              spinSOp3 N * (spinSOpPlus N - spinSOpMinus N) =
              (-(1 : ℂ)) • (spinSOpPlus N + spinSOpMinus N) := by
    rw [sub_mul, mul_sub]
    rw [show spinSOpPlus N * spinSOp3 N - spinSOpMinus N * spinSOp3 N -
            (spinSOp3 N * spinSOpPlus N - spinSOp3 N * spinSOpMinus N) =
          -(spinSOp3 N * spinSOpPlus N - spinSOpPlus N * spinSOp3 N) +
          (spinSOp3 N * spinSOpMinus N - spinSOpMinus N * spinSOp3 N) from by abel]
    rw [spinSOp3_commutator_spinSOpPlus, spinSOp3_commutator_spinSOpMinus]
    rw [neg_smul, one_smul]
    abel
  rw [hexp]
  rw [smul_smul, smul_smul]
  congr 1
  -- Goal: (1/(2*I)) * -1 = I * (1/2)
  -- i.e., -1/(2I) = I/2  ⟺  -1 = I*I  ✓
  rw [show (1 / (2 * I) : ℂ) = -I / 2 from by
    rw [show (1 / (2 * I) : ℂ) = (1 / 2) * (1 / I) from by ring]
    rw [show (1 / I : ℂ) = -I from by rw [one_div, Complex.inv_I]]
    ring]
  ring

end LatticeSystem.Quantum
