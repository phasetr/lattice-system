/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinOne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Basis states and raising/lowering operators for S = 1

Formalizes Tasaki *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1, eqs. (2.1.2), (2.1.3), (2.1.6) for the `S = 1` case.

* Computational-basis column vectors `|ψ^{+1}⟩`, `|ψ^{0}⟩`, `|ψ^{-1}⟩`
  (eq. (2.1.6) for `S = 1`, `σ ∈ {-1, 0, +1}`).
* Eigenvalue equation (eq. (2.1.2)):
  `Ŝ^(3) |ψ^{+1}⟩ = |ψ^{+1}⟩`,
  `Ŝ^(3) |ψ^{0}⟩ = 0`,
  `Ŝ^(3) |ψ^{-1}⟩ = -|ψ^{-1}⟩`.
* Raising/lowering operators `Ŝ^± := Ŝ^(1) ± i · Ŝ^(2)` with explicit
  matrix form and the defining identity.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Basis states (Tasaki eq 2.1.6, p. 14, S = 1) -/

/-- The computational-basis state `|ψ^{+1}⟩ = (1, 0, 0)ᵀ`. -/
def spinOnePlus : Fin 3 → ℂ := ![1, 0, 0]

/-- The computational-basis state `|ψ^{0}⟩ = (0, 1, 0)ᵀ`. -/
def spinOneZero : Fin 3 → ℂ := ![0, 1, 0]

/-- The computational-basis state `|ψ^{-1}⟩ = (0, 0, 1)ᵀ`. -/
def spinOneMinus : Fin 3 → ℂ := ![0, 0, 1]

/-! ## Eigenvalue equation (Tasaki eq 2.1.2, p. 14, S = 1) -/

/-- `Ŝ^(3) |ψ^{+1}⟩ = |ψ^{+1}⟩`. -/
theorem spinOneOp3_mulVec_spinOnePlus :
    spinOneOp3.mulVec spinOnePlus = spinOnePlus := by
  ext i
  fin_cases i <;>
    simp [spinOneOp3, spinOnePlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^(3) |ψ^{0}⟩ = 0`. -/
theorem spinOneOp3_mulVec_spinOneZero :
    spinOneOp3.mulVec spinOneZero = 0 := by
  ext i
  fin_cases i <;>
    simp [spinOneOp3, spinOneZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^(3) |ψ^{-1}⟩ = -|ψ^{-1}⟩`. -/
theorem spinOneOp3_mulVec_spinOneMinus :
    spinOneOp3.mulVec spinOneMinus = -spinOneMinus := by
  ext i
  fin_cases i <;>
    simp [spinOneOp3, spinOneMinus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-! ## Raising and lowering operators (Tasaki, S = 1) -/

/-- The raising operator `Ŝ^+` for `S = 1`:
`!![0, √2, 0; 0, 0, √2; 0, 0, 0]`. -/
noncomputable def spinOneOpPlus : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (Real.sqrt 2 : ℂ), 0;
     0, 0, (Real.sqrt 2 : ℂ);
     0, 0, 0]

/-- The lowering operator `Ŝ^-` for `S = 1`:
`!![0, 0, 0; √2, 0, 0; 0, √2, 0]`. -/
noncomputable def spinOneOpMinus : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     (Real.sqrt 2 : ℂ), 0, 0;
     0, (Real.sqrt 2 : ℂ), 0]

/-! ## Raising/lowering actions (Tasaki eq 2.1.3, p. 14, S = 1) -/

/-- `Ŝ^+ |ψ^{+1}⟩ = 0`. -/
theorem spinOneOpPlus_mulVec_spinOnePlus :
    spinOneOpPlus.mulVec spinOnePlus = 0 := by
  ext i
  fin_cases i <;>
    simp [spinOneOpPlus, spinOnePlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^+ |ψ^{0}⟩ = √2 · |ψ^{+1}⟩`. -/
theorem spinOneOpPlus_mulVec_spinOneZero :
    spinOneOpPlus.mulVec spinOneZero = (Real.sqrt 2 : ℂ) • spinOnePlus := by
  ext i
  fin_cases i <;>
    simp [spinOneOpPlus, spinOneZero, spinOnePlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^+ |ψ^{-1}⟩ = √2 · |ψ^{0}⟩`. -/
theorem spinOneOpPlus_mulVec_spinOneMinus :
    spinOneOpPlus.mulVec spinOneMinus = (Real.sqrt 2 : ℂ) • spinOneZero := by
  ext i
  fin_cases i <;>
    simp [spinOneOpPlus, spinOneMinus, spinOneZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^- |ψ^{+1}⟩ = √2 · |ψ^{0}⟩`. -/
theorem spinOneOpMinus_mulVec_spinOnePlus :
    spinOneOpMinus.mulVec spinOnePlus = (Real.sqrt 2 : ℂ) • spinOneZero := by
  ext i
  fin_cases i <;>
    simp [spinOneOpMinus, spinOnePlus, spinOneZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^- |ψ^{0}⟩ = √2 · |ψ^{-1}⟩`. -/
theorem spinOneOpMinus_mulVec_spinOneZero :
    spinOneOpMinus.mulVec spinOneZero = (Real.sqrt 2 : ℂ) • spinOneMinus := by
  ext i
  fin_cases i <;>
    simp [spinOneOpMinus, spinOneZero, spinOneMinus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `Ŝ^- |ψ^{-1}⟩ = 0`. -/
theorem spinOneOpMinus_mulVec_spinOneMinus :
    spinOneOpMinus.mulVec spinOneMinus = 0 := by
  ext i
  fin_cases i <;>
    simp [spinOneOpMinus, spinOneMinus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-! ## Ladder operators as `Ŝ^(1) ± i·Ŝ^(2)` (Tasaki eq (2.1.5), S = 1)

The unique non-trivial entries on either side are at indices `(0, 1)`
and `(1, 2)` for `Ŝ^+` (resp. `(1, 0)` and `(2, 1)` for `Ŝ^-`). At
those entries the right-hand side reduces to `2·invSqrt2 = √2` via
`sqrt2_mul_sqrt2` already declared just below. We use that fact in
the `linear_combination` proof. -/

/-- `Ŝ^+ = Ŝ^(1) + i·Ŝ^(2)` for `S = 1`. -/
theorem spinOneOpPlus_eq_add :
    spinOneOpPlus = spinOneOp1 + Complex.I • spinOneOp2 := by
  unfold spinOneOpPlus spinOneOp1 spinOneOp2
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hsq : ((Real.sqrt 2 : ℂ))^2 = 2 := by rw [sq]; exact h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.add_apply, invSqrt2]
     try (field_simp; rw [show (Complex.I)^2 = -1 from Complex.I_sq]; ring_nf
          try (rw [hsq])))

/-- `Ŝ^- = Ŝ^(1) - i·Ŝ^(2)` for `S = 1`. -/
theorem spinOneOpMinus_eq_sub :
    spinOneOpMinus = spinOneOp1 - Complex.I • spinOneOp2 := by
  unfold spinOneOpMinus spinOneOp1 spinOneOp2
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hsq : ((Real.sqrt 2 : ℂ))^2 = 2 := by rw [sq]; exact h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.sub_apply, invSqrt2]
     try (field_simp; rw [show (Complex.I)^2 = -1 from Complex.I_sq]; ring_nf
          try (rw [hsq])))

/-! ## Adjoint and ladder commutator (S = 1) -/

/-- `(Ŝ^+)† = Ŝ^-` for `S = 1`. -/
theorem spinOneOpPlus_conjTranspose :
    (spinOneOpPlus).conjTranspose = spinOneOpMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinOneOpPlus, spinOneOpMinus, Matrix.conjTranspose_apply]

/-- `(Ŝ^-)† = Ŝ^+` for `S = 1`. -/
theorem spinOneOpMinus_conjTranspose :
    (spinOneOpMinus).conjTranspose = spinOneOpPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinOneOpPlus, spinOneOpMinus, Matrix.conjTranspose_apply]

private lemma sqrt2_mul_sqrt2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-! ## S = 1 π-rotation matrices (Tasaki eq (2.1.33))

For `S = 1`, `(Ŝ^(α))^2 = Ŝ^(α)` fails and instead
`e^{-iπ Ŝ^(α)} = 1̂ - 2(Ŝ^(α))²`. The explicit 3×3 matrices are:

```
û_1 = !![0, 0, -1; 0, -1, 0; -1, 0, 0]
û_2 = !![0, 0,  1; 0, -1, 0;  1, 0, 0]
û_3 = !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
```
-/

/-- S = 1 π-rotation matrix about axis 1, `û_1 = e^{-iπ Ŝ^(1)}`. -/
def spinOnePiRot1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, -1;
     0, -1, 0;
     -1, 0, 0]

/-- S = 1 π-rotation matrix about axis 2, `û_2 = e^{-iπ Ŝ^(2)}`. -/
def spinOnePiRot2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1;
     0, -1, 0;
     1, 0, 0]

/-- S = 1 π-rotation matrix about axis 3, `û_3 = e^{-iπ Ŝ^(3)}`. -/
def spinOnePiRot3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- `û_3 = 1̂ - 2 · (Ŝ^(3))²` for α = 3. -/
theorem spinOnePiRot3_eq :
    (spinOnePiRot3 : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - (2 : ℂ) • (spinOneOp3 * spinOneOp3) := by
  unfold spinOnePiRot3 spinOneOp3
  ext i j
  fin_cases i <;> fin_cases j <;> first | (simp; norm_num) | simp

/-! ## Squared π-rotation identity for integer spin (Tasaki eq (2.1.31), S = 1)

For integer spin, `(û_α)^2 = 1̂`, in contrast to `(û_α)^2 = -1̂` for
half-odd-integer spin (cf. Tasaki eq. (2.1.31) vs. (2.1.27)). -/

/-- `(û_1)² = 1` for `S = 1`. -/
theorem spinOnePiRot1_sq : spinOnePiRot1 * spinOnePiRot1 = 1 := by
  unfold spinOnePiRot1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `(û_2)² = 1` for `S = 1`. -/
theorem spinOnePiRot2_sq : spinOnePiRot2 * spinOnePiRot2 = 1 := by
  unfold spinOnePiRot2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- `(û_3)² = 1` for `S = 1`. -/
theorem spinOnePiRot3_sq : spinOnePiRot3 * spinOnePiRot3 = 1 := by
  unfold spinOnePiRot3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## Integer spin commutation of π-rotations

For integer spin, distinct-axis `û_α` and `û_β` commute (unlike the
half-odd-integer case (2.1.25) where they anticommute). -/

/-- For `S = 1`, `û_1 · û_2 = û_2 · û_1`. -/
theorem spinOnePiRot1_comm_spinOnePiRot2 :
    spinOnePiRot1 * spinOnePiRot2 = spinOnePiRot2 * spinOnePiRot1 := by
  unfold spinOnePiRot1 spinOnePiRot2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- For `S = 1`, `û_2 · û_3 = û_3 · û_2`. -/
theorem spinOnePiRot2_comm_spinOnePiRot3 :
    spinOnePiRot2 * spinOnePiRot3 = spinOnePiRot3 * spinOnePiRot2 := by
  unfold spinOnePiRot2 spinOnePiRot3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- For `S = 1`, `û_3 · û_1 = û_1 · û_3`. -/
theorem spinOnePiRot3_comm_spinOnePiRot1 :
    spinOnePiRot3 * spinOnePiRot1 = spinOnePiRot1 * spinOnePiRot3 := by
  unfold spinOnePiRot3 spinOnePiRot1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## S = 1 closed-form rotation (Tasaki Problem 2.1.c)

For `S = 1`, the closed form analogue of Tasaki eq. (2.1.26) reads
`Û^(α)_θ = 1̂ - i sin θ · Ŝ^(α) - (1 - cos θ) · (Ŝ^(α))²`.
-/

/-- S = 1 closed-form rotation about axis 3.
`Û^(3)_θ = 1 - i sin θ · Ŝ^(3) - (1 - cos θ) · (Ŝ^(3))²`. -/
noncomputable def spinOneRot3 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  1 - (Complex.I * (Real.sin θ : ℂ)) • spinOneOp3 -
    ((1 : ℂ) - (Real.cos θ : ℂ)) • (spinOneOp3 * spinOneOp3)

/-- `Û^(3)_0 = 1` for S = 1. -/
theorem spinOneRot3_zero : spinOneRot3 0 = 1 := by
  unfold spinOneRot3
  simp [Real.sin_zero, Real.cos_zero]

/-- `Û^(3)_π = û_3` for S = 1. -/
theorem spinOneRot3_pi : spinOneRot3 Real.pi = spinOnePiRot3 := by
  unfold spinOneRot3
  rw [spinOnePiRot3_eq]
  simp [Real.sin_pi, Real.cos_pi]
  ring

/-- S = 1 closed-form rotation about axis 1.
`Û^(1)_θ = 1 - i sin θ · Ŝ^(1) - (1 - cos θ) · (Ŝ^(1))²`. -/
noncomputable def spinOneRot1 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  1 - (Complex.I * (Real.sin θ : ℂ)) • spinOneOp1 -
    ((1 : ℂ) - (Real.cos θ : ℂ)) • (spinOneOp1 * spinOneOp1)

/-- S = 1 closed-form rotation about axis 2.
`Û^(2)_θ = 1 - i sin θ · Ŝ^(2) - (1 - cos θ) · (Ŝ^(2))²`. -/
noncomputable def spinOneRot2 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  1 - (Complex.I * (Real.sin θ : ℂ)) • spinOneOp2 -
    ((1 : ℂ) - (Real.cos θ : ℂ)) • (spinOneOp2 * spinOneOp2)

/-- `Û^(1)_0 = 1` for S = 1. -/
theorem spinOneRot1_zero : spinOneRot1 0 = 1 := by
  unfold spinOneRot1
  simp [Real.sin_zero, Real.cos_zero]

/-- `Û^(2)_0 = 1` for S = 1. -/
theorem spinOneRot2_zero : spinOneRot2 0 = 1 := by
  unfold spinOneRot2
  simp [Real.sin_zero, Real.cos_zero]

/-- `û_1 = 1̂ - 2 · (Ŝ^(1))²` for α = 1 (Tasaki eq (2.1.30) for S = 1). -/
theorem spinOnePiRot1_eq :
    (spinOnePiRot1 : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - (2 : ℂ) • (spinOneOp1 * spinOneOp1) := by
  rw [spinOneOp1_mul_self]
  unfold spinOnePiRot1
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp; try ring)

/-- `û_2 = 1̂ - 2 · (Ŝ^(2))²` for α = 2. -/
theorem spinOnePiRot2_eq :
    (spinOnePiRot2 : Matrix (Fin 3) (Fin 3) ℂ) =
      1 - (2 : ℂ) • (spinOneOp2 * spinOneOp2) := by
  rw [spinOneOp2_mul_self]
  unfold spinOnePiRot2
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp; try ring)

/-- `Û^(1)_π = û_1` for S = 1. -/
theorem spinOneRot1_pi : spinOneRot1 Real.pi = spinOnePiRot1 := by
  unfold spinOneRot1
  rw [spinOnePiRot1_eq]
  simp [Real.sin_pi, Real.cos_pi]
  ring

/-- `Û^(2)_π = û_2` for S = 1. -/
theorem spinOneRot2_pi : spinOneRot2 Real.pi = spinOnePiRot2 := by
  unfold spinOneRot2
  rw [spinOnePiRot2_eq]
  simp [Real.sin_pi, Real.cos_pi]
  ring

/-! ## Tasaki Problem 2.1.g / eq (2.1.34): action of `û_α` on the
spin-1 basis states `|ψ^{+1,0,-1}⟩`. The matrix elements
`⟨ψ^σ| û_α |ψ^τ⟩` reduce to a small set of values:
- `û_3 |ψ^σ⟩ = e^{-iπσ} |ψ^σ⟩` (diagonal: `+1` at σ=0, `-1` at σ=±1).
- `û_2 |ψ^σ⟩ = (-1)^{1+σ} |ψ^{-σ}⟩` (off-diagonal anti-flip).
- `û_1 |ψ^σ⟩ = (-1) |ψ^{-σ}⟩` (off-diagonal anti-flip with global sign). -/

/-- `û_3 |ψ^+⟩ = -|ψ^+⟩`. -/
theorem spinOnePiRot3_mulVec_spinOnePlus :
    spinOnePiRot3.mulVec spinOnePlus = -1 • spinOnePlus := by
  unfold spinOnePiRot3 spinOnePlus
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_3 |ψ^0⟩ = |ψ^0⟩`. -/
theorem spinOnePiRot3_mulVec_spinOneZero :
    spinOnePiRot3.mulVec spinOneZero = spinOneZero := by
  unfold spinOnePiRot3 spinOneZero
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_3 |ψ^-⟩ = -|ψ^-⟩`. -/
theorem spinOnePiRot3_mulVec_spinOneMinus :
    spinOnePiRot3.mulVec spinOneMinus = -1 • spinOneMinus := by
  unfold spinOnePiRot3 spinOneMinus
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_2 |ψ^+⟩ = |ψ^-⟩`. -/
theorem spinOnePiRot2_mulVec_spinOnePlus :
    spinOnePiRot2.mulVec spinOnePlus = spinOneMinus := by
  unfold spinOnePiRot2 spinOnePlus spinOneMinus
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_2 |ψ^0⟩ = -|ψ^0⟩`. -/
theorem spinOnePiRot2_mulVec_spinOneZero :
    spinOnePiRot2.mulVec spinOneZero = -1 • spinOneZero := by
  unfold spinOnePiRot2 spinOneZero
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_2 |ψ^-⟩ = |ψ^+⟩`. -/
theorem spinOnePiRot2_mulVec_spinOneMinus :
    spinOnePiRot2.mulVec spinOneMinus = spinOnePlus := by
  unfold spinOnePiRot2 spinOneMinus spinOnePlus
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_1 |ψ^+⟩ = -|ψ^-⟩`. -/
theorem spinOnePiRot1_mulVec_spinOnePlus :
    spinOnePiRot1.mulVec spinOnePlus = -1 • spinOneMinus := by
  unfold spinOnePiRot1 spinOnePlus spinOneMinus
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_1 |ψ^0⟩ = -|ψ^0⟩`. -/
theorem spinOnePiRot1_mulVec_spinOneZero :
    spinOnePiRot1.mulVec spinOneZero = -1 • spinOneZero := by
  unfold spinOnePiRot1 spinOneZero
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `û_1 |ψ^-⟩ = -|ψ^+⟩`. -/
theorem spinOnePiRot1_mulVec_spinOneMinus :
    spinOnePiRot1.mulVec spinOneMinus = -1 • spinOnePlus := by
  unfold spinOnePiRot1 spinOneMinus spinOnePlus
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end LatticeSystem.Quantum
