/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinOne

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

end LatticeSystem.Quantum
