/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinOneBasis

/-!
# Polynomial-basis decomposition of 3×3 complex matrices (Tasaki Problem 2.1.a, S = 1)

This module formalizes the `S = 1` case of Tasaki *Physics and
Mathematics of Quantum Many-Body Systems*, §2.1 Problem 2.1.a (p.15,
solution S.1 on p.493). The claim is that every operator on the
3-dimensional spin-1 site Hilbert space `h_0 = ℂ³` can be written as
a polynomial in `1̂, Ŝ^(1), Ŝ^(2), Ŝ^(3)`.

The proof strategy follows Tasaki's solution S.1:

1. **Diagonal projectors via Lagrange interpolation**:
   `|ψ^σ⟩⟨ψ^σ| = ∏_{τ ≠ σ} (Ŝ^(3) - τ) / (σ - τ)` for σ ∈ {-1, 0, +1}.
   This expresses each diagonal projector as a polynomial in `Ŝ^(3)`.

2. **Off-diagonal matrix units via raising/lowering**:
   `|ψ^τ⟩⟨ψ^σ| = (suitable scalar) · (Ŝ^±)^k · |ψ^σ⟩⟨ψ^σ|` for τ ≠ σ.
   Combined with `Ŝ^± = Ŝ^(1) ± i·Ŝ^(2)`, this expresses each
   off-diagonal matrix unit as a polynomial in `Ŝ^(1), Ŝ^(2), Ŝ^(3)`.

3. **Spanning**: the 9 matrix units `{|ψ^τ⟩⟨ψ^σ|}_{τ, σ ∈ {-1, 0, +1}}`
   span `M_3(ℂ)` (entry-wise decomposition). Combined with steps 1-2,
   every 3×3 complex matrix is a polynomial in `1̂, Ŝ^(α)`.

The general `S ≥ 1` case (B-extra in the project roadmap) requires
an abstraction over `Fin (2S+1)` and is left to a future PR.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Diagonal projectors as polynomials in `Ŝ^(3)` -/

/-- The projector `|ψ^{+1}⟩⟨ψ^{+1}|` written explicitly.
Equals `(Ŝ^(3))(Ŝ^(3) + 1) / 2` by Lagrange interpolation
(see `spinOneProjPlus_eq_polynomial`). -/
def spinOneProjPlus : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- The projector `|ψ^{0}⟩⟨ψ^{0}|`.
Equals `1 - (Ŝ^(3))²`. -/
def spinOneProjZero : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 1, 0;
     0, 0, 0]

/-- The projector `|ψ^{-1}⟩⟨ψ^{-1}|`.
Equals `(Ŝ^(3) - 1)(Ŝ^(3)) / 2`. -/
def spinOneProjMinus : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 0, 0;
     0, 0, 1]

/-- Tasaki S.1 (S = 1, σ = +1): `|ψ^{+1}⟩⟨ψ^{+1}| = (Ŝ^(3))(Ŝ^(3) + 1) / 2`. -/
theorem spinOneProjPlus_eq_polynomial :
    (spinOneProjPlus : Matrix (Fin 3) (Fin 3) ℂ) =
      (1 / 2 : ℂ) • (spinOneOp3 * spinOneOp3 + spinOneOp3) := by
  unfold spinOneProjPlus spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try ring)

/-- Tasaki S.1 (S = 1, σ = 0): `|ψ^{0}⟩⟨ψ^{0}| = 1 - (Ŝ^(3))²`. -/
theorem spinOneProjZero_eq_polynomial :
    (spinOneProjZero : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - spinOneOp3 * spinOneOp3 := by
  unfold spinOneProjZero spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Tasaki S.1 (S = 1, σ = -1): `|ψ^{-1}⟩⟨ψ^{-1}| = ((Ŝ^(3))² - Ŝ^(3)) / 2`. -/
theorem spinOneProjMinus_eq_polynomial :
    (spinOneProjMinus : Matrix (Fin 3) (Fin 3) ℂ) =
      (1 / 2 : ℂ) • (spinOneOp3 * spinOneOp3 - spinOneOp3) := by
  unfold spinOneProjMinus spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try ring)

/-! ## Off-diagonal matrix units (the 6 transitions) -/

/-- The matrix unit `|ψ^{0}⟩⟨ψ^{+1}|`. Equals `(1/√2) Ŝ^- |ψ^+⟩⟨ψ^+|`
in the standard convention (see `spinOneUnit01_eq_polynomial`). -/
def spinOneUnit01 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     1, 0, 0;
     0, 0, 0]

/-- The matrix unit `|ψ^{-1}⟩⟨ψ^{+1}|`. -/
def spinOneUnit02 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 0, 0;
     1, 0, 0]

/-- The matrix unit `|ψ^{+1}⟩⟨ψ^{0}|`. -/
def spinOneUnit10 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0;
     0, 0, 0;
     0, 0, 0]

/-- The matrix unit `|ψ^{-1}⟩⟨ψ^{0}|`. -/
def spinOneUnit12 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 0, 0;
     0, 1, 0]

/-- The matrix unit `|ψ^{+1}⟩⟨ψ^{-1}|`. -/
def spinOneUnit20 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1;
     0, 0, 0;
     0, 0, 0]

/-- The matrix unit `|ψ^{0}⟩⟨ψ^{-1}|`. -/
def spinOneUnit21 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 0, 1;
     0, 0, 0]

private lemma sqrt2_sq : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `|ψ^{0}⟩⟨ψ^{+1}| = (1/√2) Ŝ^- |ψ^{+1}⟩⟨ψ^{+1}|`. -/
theorem spinOneUnit01_eq_polynomial :
    (spinOneUnit01 : Matrix (Fin 3) (Fin 3) ℂ) =
      ((Real.sqrt 2 : ℂ)⁻¹) • (spinOneOpMinus * spinOneProjPlus) := by
  unfold spinOneUnit01 spinOneOpMinus spinOneProjPlus
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `|ψ^{+1}⟩⟨ψ^{0}| = (1/√2) Ŝ^+ |ψ^{0}⟩⟨ψ^{0}|`. -/
theorem spinOneUnit10_eq_polynomial :
    (spinOneUnit10 : Matrix (Fin 3) (Fin 3) ℂ) =
      ((Real.sqrt 2 : ℂ)⁻¹) • (spinOneOpPlus * spinOneProjZero) := by
  unfold spinOneUnit10 spinOneOpPlus spinOneProjZero
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `|ψ^{-1}⟩⟨ψ^{0}| = (1/√2) Ŝ^- |ψ^{0}⟩⟨ψ^{0}|`. -/
theorem spinOneUnit12_eq_polynomial :
    (spinOneUnit12 : Matrix (Fin 3) (Fin 3) ℂ) =
      ((Real.sqrt 2 : ℂ)⁻¹) • (spinOneOpMinus * spinOneProjZero) := by
  unfold spinOneUnit12 spinOneOpMinus spinOneProjZero
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `|ψ^{0}⟩⟨ψ^{-1}| = (1/√2) Ŝ^+ |ψ^{-1}⟩⟨ψ^{-1}|`. -/
theorem spinOneUnit21_eq_polynomial :
    (spinOneUnit21 : Matrix (Fin 3) (Fin 3) ℂ) =
      ((Real.sqrt 2 : ℂ)⁻¹) • (spinOneOpPlus * spinOneProjMinus) := by
  unfold spinOneUnit21 spinOneOpPlus spinOneProjMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `|ψ^{-1}⟩⟨ψ^{+1}| = (1/2) (Ŝ^-)² |ψ^{+1}⟩⟨ψ^{+1}|`. -/
theorem spinOneUnit02_eq_polynomial :
    (spinOneUnit02 : Matrix (Fin 3) (Fin 3) ℂ) =
      (1 / 2 : ℂ) • (spinOneOpMinus * spinOneOpMinus * spinOneProjPlus) := by
  unfold spinOneUnit02 spinOneOpMinus spinOneProjPlus
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try (rw [sqrt2_sq]; ring))

/-- `|ψ^{+1}⟩⟨ψ^{-1}| = (1/2) (Ŝ^+)² |ψ^{-1}⟩⟨ψ^{-1}|`. -/
theorem spinOneUnit20_eq_polynomial :
    (spinOneUnit20 : Matrix (Fin 3) (Fin 3) ℂ) =
      (1 / 2 : ℂ) • (spinOneOpPlus * spinOneOpPlus * spinOneProjMinus) := by
  unfold spinOneUnit20 spinOneOpPlus spinOneProjMinus
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try (rw [sqrt2_sq]; ring))

/-! ## Spanning theorem: every 3×3 complex matrix is a linear combination
of the 9 matrix units. -/

/-- Tasaki §2.1 Problem 2.1.a (S = 1, spanning step):
every 3×3 complex matrix `A` is a linear combination of the 9 matrix
units `|ψ^τ⟩⟨ψ^σ|`, with coefficients `A τ σ` (entry-wise). Combined
with the polynomial expressions for each unit (above), every such `A`
is a polynomial in `1̂, Ŝ^(1), Ŝ^(2), Ŝ^(3)`. -/
theorem spinOne_decomposition (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A = A 0 0 • spinOneProjPlus
      + A 0 1 • spinOneUnit10
      + A 0 2 • spinOneUnit20
      + A 1 0 • spinOneUnit01
      + A 1 1 • spinOneProjZero
      + A 1 2 • spinOneUnit21
      + A 2 0 • spinOneUnit02
      + A 2 1 • spinOneUnit12
      + A 2 2 • spinOneProjMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinOneProjPlus, spinOneProjZero, spinOneProjMinus,
      spinOneUnit01, spinOneUnit02, spinOneUnit10, spinOneUnit12,
      spinOneUnit20, spinOneUnit21]

end LatticeSystem.Quantum
