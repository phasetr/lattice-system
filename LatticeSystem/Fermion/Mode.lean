/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation

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

end LatticeSystem.Fermion
