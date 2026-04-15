/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import Mathlib.Tactic.LinearCombination

/-!
# Pauli-basis decomposition of 2×2 complex matrices

This module formalizes the `S = 1/2` case of Tasaki *Physics and
Mathematics of Quantum Many-Body Systems*, §2.1 Problem 2.1.a
(p. 15). The general claim is that every operator on the
`(2S+1)`-dimensional Hilbert space is a polynomial of `1`, `Ŝ^(1)`,
`Ŝ^(2)`, `Ŝ^(3)`. For `S = 1/2` the operator space is four-dimensional
and a linear combination suffices: the four matrices `1`, `σ^x`, `σ^y`,
`σ^z` span `Matrix (Fin 2) (Fin 2) ℂ`.

We state the result in two equivalent forms:

* `pauli_decomposition`: with explicit coefficients `pauliCoeff0..3`,
  `A = c₀ · 1 + c₁ · σ^x + c₂ · σ^y + c₃ · σ^z`.
* `spinHalf_decomposition`: the same decomposition expressed via
  `Ŝ^(α) = σ^(α)/2`.

We also prove linear independence of `{1, σ^x, σ^y, σ^z}`, turning the
decomposition into a full basis statement for `Matrix (Fin 2) (Fin 2) ℂ`.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Explicit coefficients -/

/-- The identity-component coefficient in the Pauli decomposition. -/
noncomputable def pauliCoeff0 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (A 0 0 + A 1 1) / 2

/-- The `σ^x`-component coefficient. -/
noncomputable def pauliCoeff1 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (A 0 1 + A 1 0) / 2

/-- The `σ^y`-component coefficient. -/
noncomputable def pauliCoeff2 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  I * (A 0 1 - A 1 0) / 2

/-- The `σ^z`-component coefficient. -/
noncomputable def pauliCoeff3 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (A 0 0 - A 1 1) / 2

/-! ## Main decomposition theorem -/

/-- Every 2×2 complex matrix is a linear combination of `1`, `σ^x`,
`σ^y`, `σ^z`, with coefficients given by `pauliCoeff0..3`. This is
the `S = 1/2` case of Tasaki Problem 2.1.a on p. 15. -/
theorem pauli_decomposition (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A = pauliCoeff0 A • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + pauliCoeff1 A • pauliX
      + pauliCoeff2 A • pauliY
      + pauliCoeff3 A • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
           pauliX, pauliY, pauliZ, Matrix.smul_apply, Matrix.add_apply]
     try ring_nf
     try simp only [Complex.I_sq]
     try ring)

/-- Counterpart of `pauli_decomposition` phrased in terms of the spin
operators `Ŝ^(α)` (Tasaki §2.1 eq. (2.1.7)). Using
`σ^(α) = 2 · Ŝ^(α)`, the coefficients double accordingly. -/
theorem spinHalf_decomposition (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A = pauliCoeff0 A • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + (2 * pauliCoeff1 A) • spinHalfOp1
      + (2 * pauliCoeff2 A) • spinHalfOp2
      + (2 * pauliCoeff3 A) • spinHalfOp3 := by
  nth_rewrite 1 [pauli_decomposition A]
  rw [pauliX_eq_two_smul_spinHalfOp1, pauliY_eq_two_smul_spinHalfOp2,
      pauliZ_eq_two_smul_spinHalfOp3,
      smul_smul, smul_smul, smul_smul,
      mul_comm (pauliCoeff1 A) 2, mul_comm (pauliCoeff2 A) 2,
      mul_comm (pauliCoeff3 A) 2]

/-! ## Linear independence -/

/-- The Pauli matrices together with the identity are linearly
independent in `Matrix (Fin 2) (Fin 2) ℂ`. Combined with
`pauli_decomposition`, this shows `{1, σ^x, σ^y, σ^z}` is a basis of
the four-dimensional space `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem pauli_linearIndep (a₀ a₁ a₂ a₃ : ℂ)
    (h : a₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + a₁ • pauliX + a₂ • pauliY + a₃ • pauliZ = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  -- Extract scalar equations by evaluating at matrix entries.
  have h00 : a₀ + a₃ = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simpa [pauliX, pauliY, pauliZ, Matrix.smul_apply, Matrix.add_apply]
      using this
  have h11 : a₀ - a₃ = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    simpa [pauliX, pauliY, pauliZ, Matrix.smul_apply, Matrix.add_apply]
      using this
  have h01 : a₁ - a₂ * I = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simpa [pauliX, pauliY, pauliZ, Matrix.smul_apply, Matrix.add_apply]
      using this
  have h10 : a₁ + a₂ * I = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
    simpa [pauliX, pauliY, pauliZ, Matrix.smul_apply, Matrix.add_apply]
      using this
  have ha0 : a₀ = 0 := by linear_combination (h00 + h11) / 2
  have ha3 : a₃ = 0 := by linear_combination (h00 - h11) / 2
  have ha1 : a₁ = 0 := by linear_combination (h01 + h10) / 2
  have ha2 : a₂ = 0 := by
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have heq : a₂ * I = 0 := by linear_combination (h10 - h01) / 2
    exact (mul_eq_zero.mp heq).resolve_right hI
  exact ⟨ha0, ha1, ha2, ha3⟩

end LatticeSystem.Quantum
