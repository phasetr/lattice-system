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

end LatticeSystem.Quantum
