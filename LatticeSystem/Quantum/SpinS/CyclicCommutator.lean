import LatticeSystem.Quantum.SpinS.Cartan3
import LatticeSystem.Quantum.SpinS.Algebra

/-!
# Cyclic SU(2) commutators `[Ŝ^{(α)}, Ŝ^{(β)}] = i ε^αβγ Ŝ^{(γ)}`
(Tasaki §2.1 P1d''' β-20, β-21, β-22)

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

/-! ## β-20: `[Ŝ^{(1)}, Ŝ^{(2)}] = i · Ŝ^{(3)}` -/

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

/-! ## β-21: `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`

The second of the three cyclic SU(2) commutators for the spin-`S`
operators on `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ`. Derived from
the Cartan relations β-2:

* `Ŝ^{(3)} Ŝ^+ - Ŝ^+ Ŝ^{(3)} = Ŝ^+`,
* `Ŝ^{(3)} Ŝ^- - Ŝ^- Ŝ^{(3)} = -Ŝ^-`,

via the expansion `Ŝ^{(2)} = (Ŝ^+ - Ŝ^-)/(2i)` together with the
identity `Ŝ^{(1)} = (Ŝ^+ + Ŝ^-)/2`:

  `[Ŝ^{(2)}, Ŝ^{(3)}] = (1/(2i)) (-Ŝ^+ - Ŝ^-) = (-1/i) Ŝ^{(1)} = i Ŝ^{(1)}`.
-/

/-- Cyclic SU(2) commutator: `[Ŝ^{(2)}, Ŝ^{(3)}] = i · Ŝ^{(1)}`. -/
theorem spinSOp2_commutator_spinSOp3 (N : ℕ) :
    spinSOp2 N * spinSOp3 N - spinSOp3 N * spinSOp2 N = I • spinSOp1 N := by
  unfold spinSOp2 spinSOp1
  rw [Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_sub]
  -- Goal: (1/(2*I)) • ((Ŝ^+ - Ŝ^-) * Ŝ^(3) - Ŝ^(3) * (Ŝ^+ - Ŝ^-))
  --         = I • ((1/2) • (Ŝ^+ + Ŝ^-))
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

/-! ## β-22: `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`

The third (and last) of the cyclic SU(2) commutators for the spin-`S`
operators on `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ`. Derived from
the Cartan relations β-2 via `Ŝ^{(1)} = (Ŝ^+ + Ŝ^-)/2`:

  `[Ŝ^{(3)}, Ŝ^{(1)}]
      = (1/2) [(Ŝ^{(3)} Ŝ^+ − Ŝ^+ Ŝ^{(3)}) + (Ŝ^{(3)} Ŝ^- − Ŝ^- Ŝ^{(3)})]
      = (1/2) (Ŝ^+ − Ŝ^-) = i · Ŝ^{(2)}`,

where the inner Cartan relations supply `Ŝ^+` and `−Ŝ^-`, and the
final scalar identity `(1/2) · (2i) = i` matches `Ŝ^{(2)} = (Ŝ^+ − Ŝ^-)/(2i)`.

Together with β-20 and β-21 this completes the standard SU(2)
commutator algebra (Tasaki eq. (2.1.1)) for spin-`S` operators.
-/

/-- Cyclic SU(2) commutator: `[Ŝ^{(3)}, Ŝ^{(1)}] = i · Ŝ^{(2)}`. -/
theorem spinSOp3_commutator_spinSOp1 (N : ℕ) :
    spinSOp3 N * spinSOp1 N - spinSOp1 N * spinSOp3 N = I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub]
  -- Goal: (1/2) • (Ŝ^(3) (Ŝ^+ + Ŝ^-) - (Ŝ^+ + Ŝ^-) Ŝ^(3))
  --         = I • ((1/(2I)) • (Ŝ^+ - Ŝ^-))
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
