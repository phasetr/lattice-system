import LatticeSystem.Quantum.SpinS.CyclicCommutator23

/-!
# Third cyclic SU(2) commutator `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`
(Tasaki §2.1 P1d''' β-22)

The third (and last) of the cyclic SU(2) commutators for the spin-`S`
operators on `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ`. Derived from
the Cartan relations β-2 via `Ŝ^{(1)} = (Ŝ^+ + Ŝ^-)/2`:

  `[Ŝ^{(3)}, Ŝ^{(1)}] = (1/2) [(Ŝ^{(3)} Ŝ^+ − Ŝ^+ Ŝ^{(3)}) + (Ŝ^{(3)} Ŝ^- − Ŝ^- Ŝ^{(3)})]
                     = (1/2) (Ŝ^+ − Ŝ^-) = i · Ŝ^{(2)}`,

where the inner Cartan relations supply `Ŝ^+` and `−Ŝ^-`, and the
final scalar identity `(1/2) · (2i) = i` matches `Ŝ^{(2)} = (Ŝ^+ − Ŝ^-)/(2i)`.

Together with β-20 and β-21 this completes the standard SU(2)
commutator algebra (Tasaki eq. (2.1.1)) for spin-`S` operators.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.1).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Cyclic SU(2) commutator: `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`. -/
theorem spinSOp3_commutator_spinSOp1 (N : ℕ) :
    spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N = I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub]
  -- Goal: (1/2) • (Ŝ^(3) (Ŝ^+ + Ŝ^-) - (Ŝ^+ + Ŝ^-) Ŝ^(3)) = I • ((1/(2I)) • (Ŝ^+ - Ŝ^-))
  have hexp : spinSOp3 N * (spinSOpPlus N + spinSOpMinus N) -
              (spinSOpPlus N + spinSOpMinus N) * spinSOp3 N =
              spinSOpPlus N - spinSOpMinus N := by
    rw [mul_add, add_mul]
    rw [show spinSOp3 N * spinSOpPlus N + spinSOp3 N * spinSOpMinus N -
            (spinSOpPlus N * spinSOp3 N + spinSOpMinus N * spinSOp3 N) =
          (spinSOp3 N * spinSOpPlus N - spinSOpPlus N * spinSOp3 N) +
          (spinSOp3 N * spinSOpMinus N - spinSOpMinus N * spinSOp3 N) from by abel]
    rw [spinSOp3_commutator_spinSOpPlus, spinSOp3_commutator_spinSOpMinus]
    abel
  rw [hexp]
  rw [smul_smul]
  congr 1
  -- Goal: 1/2 = I * (1/(2*I))
  rw [show (I : ℂ) * (1 / (2 * I)) = (I * 1) / (2 * I) from by rw [mul_div_assoc]]
  rw [mul_one]
  rw [show (I / (2 * I) : ℂ) = (1 : ℂ) / 2 from by
    rw [show (I / (2 * I) : ℂ) = I * (2 * I)⁻¹ from by rw [div_eq_mul_inv]]
    rw [mul_inv]
    rw [show (I * (2⁻¹ * I⁻¹) : ℂ) = 2⁻¹ * (I * I⁻¹) from by ring]
    rw [mul_inv_cancel₀ Complex.I_ne_zero]
    ring]

end LatticeSystem.Quantum
