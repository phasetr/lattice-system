/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalfRotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `SU(2)` parametrization (Tasaki §2.2 Problem 2.2.c preparation)

Bundles the **special unitary group** `SU(2)` of `2 × 2` complex
matrices, verifies that the spin-1/2 single-axis rotations
`spinHalfRot{1,2,3} θ` (Tasaki eq. (2.1.26)) lie in `SU(2)`, and
provides the forward Euler-angle parametrization
`(φ, θ, ψ) ↦ Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ ∈ SU(2)` needed downstream
for the SU(2)-averaged-state characterization in Tasaki §2.2
Problem 2.2.c (eq. (2.2.15)).

`SU(2)` is bundled as a `Submonoid` of `Matrix (Fin 2) (Fin 2) ℂ`,
intersection of `unitary` (`star U * U = 1 ∧ U * star U = 1`) with the
condition `Matrix.det U = 1`. Multiplicativity of `det` makes the
intersection a submonoid.

## Main definitions

* `SU2` — the submonoid of `Matrix (Fin 2) (Fin 2) ℂ` consisting of
  unitary matrices with determinant `1`.
* `spinHalfEulerProduct φ θ ψ` — the SU(2) element built from three
  Euler angles via the Z-Y-Z decomposition.

## Main theorems

* `mem_SU2_iff` — membership unfolds to `unitary ∧ det = 1`.
* `spinHalfRot{1,2,3}_mem_SU2` — each axis rotation lies in `SU(2)`.
* `spinHalfEulerProduct_mem_SU2` — the Euler-angle product lies in `SU(2)`.

The reverse direction (every `SU(2)` element decomposes into Euler
angles) is left to a future PR.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-- `SU(2)` as a submonoid of `Matrix (Fin 2) (Fin 2) ℂ`: unitary
matrices with determinant `1`. -/
def SU2 : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := { U | U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ Matrix.det U = 1 }
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := fun {U V} hU hV =>
    ⟨mul_mem hU.1 hV.1, by rw [Matrix.det_mul, hU.2, hV.2, mul_one]⟩

theorem mem_SU2_iff (U : Matrix (Fin 2) (Fin 2) ℂ) :
    U ∈ SU2 ↔ U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ Matrix.det U = 1 :=
  Iff.rfl

/-! ## Spin-1/2 rotations are unitary -/

/-- `Û^(1)_θ ∈ unitary`. -/
theorem spinHalfRot1_mem_unitary (θ : ℝ) :
    spinHalfRot1 θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [show star (spinHalfRot1 θ) = (spinHalfRot1 θ).conjTranspose from rfl,
      spinHalfRot1_adjoint]
    rw [spinHalfRot1_mul, neg_add_cancel, spinHalfRot1_zero]
  · rw [show star (spinHalfRot1 θ) = (spinHalfRot1 θ).conjTranspose from rfl]
    exact spinHalfRot1_unitary θ

/-- `Û^(2)_θ ∈ unitary`. -/
theorem spinHalfRot2_mem_unitary (θ : ℝ) :
    spinHalfRot2 θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [show star (spinHalfRot2 θ) = (spinHalfRot2 θ).conjTranspose from rfl,
      spinHalfRot2_adjoint]
    rw [spinHalfRot2_mul, neg_add_cancel, spinHalfRot2_zero]
  · rw [show star (spinHalfRot2 θ) = (spinHalfRot2 θ).conjTranspose from rfl]
    exact spinHalfRot2_unitary θ

/-- `Û^(3)_θ ∈ unitary`. -/
theorem spinHalfRot3_mem_unitary (θ : ℝ) :
    spinHalfRot3 θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [show star (spinHalfRot3 θ) = (spinHalfRot3 θ).conjTranspose from rfl,
      spinHalfRot3_adjoint]
    rw [spinHalfRot3_mul, neg_add_cancel, spinHalfRot3_zero]
  · rw [show star (spinHalfRot3 θ) = (spinHalfRot3 θ).conjTranspose from rfl]
    exact spinHalfRot3_unitary θ

/-! ## Spin-1/2 rotations are in SU(2) -/

/-- `Û^(1)_θ ∈ SU(2)`. -/
theorem spinHalfRot1_mem_SU2 (θ : ℝ) : spinHalfRot1 θ ∈ SU2 :=
  ⟨spinHalfRot1_mem_unitary θ, spinHalfRot1_det_eq_one θ⟩

/-- `Û^(2)_θ ∈ SU(2)`. -/
theorem spinHalfRot2_mem_SU2 (θ : ℝ) : spinHalfRot2 θ ∈ SU2 :=
  ⟨spinHalfRot2_mem_unitary θ, spinHalfRot2_det_eq_one θ⟩

/-- `Û^(3)_θ ∈ SU(2)`. -/
theorem spinHalfRot3_mem_SU2 (θ : ℝ) : spinHalfRot3 θ ∈ SU2 :=
  ⟨spinHalfRot3_mem_unitary θ, spinHalfRot3_det_eq_one θ⟩

/-! ## Forward Euler-angle parametrization -/

/-- The SU(2) element built from three Euler angles `(φ, θ, ψ)` via
the standard Z-Y-Z decomposition: `Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ`.
This is the parametrization used in Tasaki §2.2 Problem 2.2.c
(eq. (2.2.15)). -/
noncomputable def spinHalfEulerProduct (φ θ ψ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  spinHalfRot3 φ * spinHalfRot2 θ * spinHalfRot3 ψ

/-- The Euler-angle product is unitary. -/
theorem spinHalfEulerProduct_mem_unitary (φ θ ψ : ℝ) :
    spinHalfEulerProduct φ θ ψ ∈
      unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  mul_mem (mul_mem (spinHalfRot3_mem_unitary φ) (spinHalfRot2_mem_unitary θ))
    (spinHalfRot3_mem_unitary ψ)

/-- The Euler-angle product lies in `SU(2)`. -/
theorem spinHalfEulerProduct_mem_SU2 (φ θ ψ : ℝ) :
    spinHalfEulerProduct φ θ ψ ∈ SU2 :=
  mul_mem (mul_mem (spinHalfRot3_mem_SU2 φ) (spinHalfRot2_mem_SU2 θ))
    (spinHalfRot3_mem_SU2 ψ)

end LatticeSystem.Quantum
