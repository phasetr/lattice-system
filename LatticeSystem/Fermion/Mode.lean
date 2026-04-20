/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import LatticeSystem.Quantum.SpinHalfBasis

/-!
# Single-mode fermion creation and annihilation operators

This module defines the smallest concrete piece of the
canonical anticommutation (CAR) algebra: the creation and
annihilation operators of a single fermion mode, acting on the
two-dimensional Hilbert space `ℂ²` with computational basis
`|0⟩ = e₀` (vacuum) and `|1⟩ = e₁` (occupied).

The matrix conventions are

```
c  = |0⟩⟨1| = !![0, 1; 0, 0]
c† = |1⟩⟨0| = !![0, 0; 1, 0]
n  = c†·c   = !![0, 0; 0, 1]
```

We prove the defining single-mode CAR relations:

* `c² = 0` (`fermionAnnihilation_sq`).
* `(c†)² = 0` (`fermionCreation_sq`).
* `c·c† + c†·c = 1` (`fermionAnticomm_self`).
* `n² = n` (`fermionNumber_sq`), the idempotency of the number
  operator with eigenvalues `0` and `1`.
* Hermiticity: `cᴴ = c†`, `(c†)ᴴ = c`, and `n` is Hermitian.

This is the building block for the multi-mode CAR algebra (constructed
via the Jordan–Wigner mapping using the spin infrastructure in
`LatticeSystem/Quantum/`) and ultimately the Hubbard / BCS Hamiltonians
of Phase 2.
-/

namespace LatticeSystem.Fermion

open Matrix

/-! ## Definitions -/

/-- Single-mode fermion annihilation operator `c = |0⟩⟨1|`. -/
def fermionAnnihilation : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- Single-mode fermion creation operator `c† = |1⟩⟨0|`. -/
def fermionCreation : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 1, 0]

/-- Single-mode fermion number operator `n = c† · c = |1⟩⟨1|`. -/
def fermionNumber : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

/-! ## Number operator equals `c† · c` -/

/-- The number operator equals the product `c† · c`. -/
theorem fermionNumber_eq_creation_mul_annihilation :
    fermionNumber = fermionCreation * fermionAnnihilation := by
  unfold fermionNumber fermionCreation fermionAnnihilation
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## CAR relations -/

/-- `c² = 0`. -/
theorem fermionAnnihilation_sq :
    fermionAnnihilation * fermionAnnihilation = 0 := by
  unfold fermionAnnihilation
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `(c†)² = 0`. -/
theorem fermionCreation_sq :
    fermionCreation * fermionCreation = 0 := by
  unfold fermionCreation
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The single-mode canonical anticommutation relation:
`c · c† + c† · c = 1`. -/
theorem fermionAnticomm_self :
    fermionAnnihilation * fermionCreation
      + fermionCreation * fermionAnnihilation = 1 := by
  unfold fermionAnnihilation fermionCreation
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## Number operator: idempotency -/

/-- The number operator is idempotent: `n² = n` (eigenvalues `0` and `1`). -/
theorem fermionNumber_sq :
    fermionNumber * fermionNumber = fermionNumber := by
  unfold fermionNumber
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## Hermiticity / conjugate transpose -/

/-- `(c)ᴴ = c†`: the annihilation operator's adjoint is the creation
operator. -/
theorem fermionAnnihilation_conjTranspose :
    (fermionAnnihilation)ᴴ = fermionCreation := by
  unfold fermionAnnihilation fermionCreation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- `(c†)ᴴ = c`: the creation operator's adjoint is the annihilation
operator. -/
theorem fermionCreation_conjTranspose :
    (fermionCreation)ᴴ = fermionAnnihilation := by
  unfold fermionAnnihilation fermionCreation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- The number operator is Hermitian: `nᴴ = n`. -/
theorem fermionNumber_isHermitian : fermionNumber.IsHermitian := by
  unfold fermionNumber
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-! ## Basis vectors and basis action -/

/-- Vacuum basis vector `|0⟩ = (1, 0)`. -/
def fermionVacuum : Fin 2 → ℂ := ![1, 0]

/-- Occupied basis vector `|1⟩ = (0, 1)`. -/
def fermionOccupied : Fin 2 → ℂ := ![0, 1]

/-- `c|0⟩ = 0`: the annihilation operator destroys the vacuum. -/
theorem fermionAnnihilation_mulVec_vacuum :
    fermionAnnihilation.mulVec fermionVacuum = 0 := by
  unfold fermionAnnihilation fermionVacuum
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `c|1⟩ = |0⟩`: the annihilation operator removes the particle. -/
theorem fermionAnnihilation_mulVec_occupied :
    fermionAnnihilation.mulVec fermionOccupied = fermionVacuum := by
  unfold fermionAnnihilation fermionOccupied fermionVacuum
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `c†|0⟩ = |1⟩`: the creation operator adds a particle to the vacuum. -/
theorem fermionCreation_mulVec_vacuum :
    fermionCreation.mulVec fermionVacuum = fermionOccupied := by
  unfold fermionCreation fermionVacuum fermionOccupied
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `c†|1⟩ = 0`: cannot add a second particle (Pauli exclusion). -/
theorem fermionCreation_mulVec_occupied :
    fermionCreation.mulVec fermionOccupied = 0 := by
  unfold fermionCreation fermionOccupied
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `n|0⟩ = 0`: vacuum has no particles. -/
theorem fermionNumber_mulVec_vacuum :
    fermionNumber.mulVec fermionVacuum = 0 := by
  unfold fermionNumber fermionVacuum
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `n|1⟩ = |1⟩`: occupied state has one particle. -/
theorem fermionNumber_mulVec_occupied :
    fermionNumber.mulVec fermionOccupied = fermionOccupied := by
  unfold fermionNumber fermionOccupied
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## Identification with spin-1/2 raising / lowering operators

In the computational basis, the single-mode fermion creation /
annihilation operators are exactly the spin-1/2 raising / lowering
operators:

  `c = σ^+`  (annihilation = raising)
  `c† = σ^-` (creation = lowering)

This is the algebraic basis of the Jordan–Wigner mapping that lifts
the single-mode CAR algebra to the multi-mode case using the existing
spin infrastructure.
-/

/-- `c = σ^+` (annihilation equals raising in the computational basis). -/
theorem fermionAnnihilation_eq_spinHalfOpPlus :
    fermionAnnihilation = LatticeSystem.Quantum.spinHalfOpPlus := by
  unfold fermionAnnihilation
  rfl

/-- `c† = σ^-` (creation equals lowering in the computational basis). -/
theorem fermionCreation_eq_spinHalfOpMinus :
    fermionCreation = LatticeSystem.Quantum.spinHalfOpMinus := by
  unfold fermionCreation
  rfl

end LatticeSystem.Fermion
