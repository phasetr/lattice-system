import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFockDown

/-!
# The block kinetic operator acts as `A·C + C·B` on the coefficient matrix (Tasaki §10.2.1)

Tenth layer (PR10) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

The gauge independence of PR8/PR9 means the up- and down-kinetic actions on the
block coefficient matrix are given by *fixed* matrices. This file packages them as
honest matrix multiplications: the up kinetic acts as left multiplication
`C ↦ A·C` and the down kinetic as right multiplication `C ↦ C·Bᵣ`, so the
spin-symmetric block kinetic operator acts as `C ↦ A·C + C·Bᵣ`.

## Main definitions

* `hubbardBlockKineticUpFixedMatrix` / `hubbardBlockKineticDownFixedRightMatrix` —
  the fixed left/right multiplier matrices (the gauge-independent per-column /
  transposed per-row matrices).
* `hubbardBlockKinetic` / `hubbardBlockKineticCoeffAction` — the spin-symmetric
  block kinetic operator and its coefficient-matrix action `A·C + C·Bᵣ`.

## Main results

* `hubbardBlockKineticUpCoeffAction_eq_mul_fixed` — `up action = A·C`.
* `hubbardBlockKineticDownCoeffAction_eq_mul_fixedRight` — `down action = C·Bᵣ`.
* `hubbardBlockCoeff_hubbardBlockKinetic_mulVec` — the block kinetic operator acts
  on the block coefficient matrix as `C ↦ A·C + C·Bᵣ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The fixed left-multiplier matrix of the up kinetic operator (the
gauge-independent per-column matrix, evaluated at the reference hole `0`). -/
noncomputable def hubbardBlockKineticUpFixedMatrix (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  hubbardBlockKineticUpCoeffMatrix N T (fun _ => 0)

/-- The fixed right-multiplier matrix of the down kinetic operator (the transpose
of the gauge-independent per-row matrix, evaluated at the reference up `0`). -/
noncomputable def hubbardBlockKineticDownFixedRightMatrix (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  (hubbardBlockKineticDownCoeffMatrix N T (fun _ => 0))ᵀ

/-- The up-kinetic coefficient action is left multiplication by the fixed matrix. -/
theorem hubbardBlockKineticUpCoeffAction_eq_mul_fixed (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    hubbardBlockKineticUpCoeffAction N T C
      = hubbardBlockKineticUpFixedMatrix N T * C := by
  funext u h
  unfold hubbardBlockKineticUpCoeffAction
  rw [hubbardBlockKineticUpCoeffMatrix_indep_down N T h (fun _ => 0)]
  simp only [hubbardBlockKineticUpFixedMatrix, Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- The down-kinetic coefficient action is right multiplication by the fixed
(transposed) matrix. -/
theorem hubbardBlockKineticDownCoeffAction_eq_mul_fixedRight (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    hubbardBlockKineticDownCoeffAction N T C
      = C * hubbardBlockKineticDownFixedRightMatrix N T := by
  funext u h
  unfold hubbardBlockKineticDownCoeffAction
  rw [hubbardBlockKineticDownCoeffMatrix_indep_up N T u (fun _ => 0)]
  simp only [hubbardBlockKineticDownFixedRightMatrix, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun h' _ => mul_comm _ _)

/-! ## The combined block kinetic operator -/

/-- The block-order spin-symmetric kinetic operator `Ĥ↑ + Ĥ↓`. -/
noncomputable def hubbardBlockKinetic (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardBlockKineticUp N T + hubbardBlockKineticDown N T

/-- The block kinetic coefficient-matrix action `C ↦ A·C + C·Bᵣ`. -/
noncomputable def hubbardBlockKineticCoeffAction (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  hubbardBlockKineticUpFixedMatrix N T * C +
    C * hubbardBlockKineticDownFixedRightMatrix N T

/-- The block coefficient matrix is additive in the state vector. -/
theorem hubbardBlockCoeff_add (N : ℕ)
    (ψ φ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N (ψ + φ) = hubbardBlockCoeff N ψ + hubbardBlockCoeff N φ := by
  funext u h; simp [hubbardBlockCoeff]

/-- **The block kinetic operator acts on the block coefficient matrix as
`C ↦ A·C + C·Bᵣ`.** -/
theorem hubbardBlockCoeff_hubbardBlockKinetic_mulVec (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N ((hubbardBlockKinetic N T).mulVec ψ)
      = hubbardBlockKineticCoeffAction N T (hubbardBlockCoeff N ψ) := by
  rw [hubbardBlockKinetic, Matrix.add_mulVec, hubbardBlockCoeff_add,
    hubbardBlockCoeff_hubbardBlockKineticUp_mulVec,
    hubbardBlockCoeff_hubbardBlockKineticDown_mulVec,
    hubbardBlockKineticUpCoeffAction_eq_mul_fixed,
    hubbardBlockKineticDownCoeffAction_eq_mul_fixedRight,
    hubbardBlockKineticCoeffAction]

end LatticeSystem.Fermion
