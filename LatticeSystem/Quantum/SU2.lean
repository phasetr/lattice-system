/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalfRotation

/-!
# Single-spin rotation submonoid (Tasaki §2.2 Problem 2.2.c preparation)

Bundles the **single-spin unitary group** `U(2)` of `2 × 2` complex
matrices, verifies that the spin-1/2 single-axis rotations
`spinHalfRot{1,2,3} θ` (Tasaki eq. (2.1.26)) lie in `U(2)`, and
provides the forward Euler-angle parametrization
`(φ, θ, ψ) ↦ Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ ∈ U(2)` needed downstream
for the SU(2)-averaged-state characterization in Tasaki §2.2
Problem 2.2.c (eq. (2.2.15)).

## Notes on `U(2)` vs `SU(2)`

Tasaki's spin-1/2 rotations actually lie in the *special* unitary
group `SU(2)` (determinant 1). For the purposes of Problem 2.2.c the
unitary structure is what is integrated against, and the
det = 1 specialization is not strictly needed. We therefore work with
the unitary submonoid `unitary (Matrix (Fin 2) (Fin 2) ℂ)` and
defer the explicit `det = 1` proofs to a follow-up PR (the
straightforward calculation is `cos²(θ/2) + sin²(θ/2) = 1` per axis,
which is a Pythagorean identity but requires nontrivial
Real-vs-Complex casting in Lean).

## Main definitions

* `spinHalfEulerProduct φ θ ψ` — the Euler-angle product
  `Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ` as an element of
  `Matrix (Fin 2) (Fin 2) ℂ`.

## Main theorems

* `spinHalfRot{1,2,3}_mem_unitary`: each axis rotation lies in
  `unitary (Matrix (Fin 2) (Fin 2) ℂ)`.
* `spinHalfEulerProduct_mem_unitary`: the Euler-angle product lies in
  `unitary (Matrix (Fin 2) (Fin 2) ℂ)`.

The reverse direction (every `U(2)` element decomposes into Euler
angles) is left to a future PR.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Spin-1/2 rotations are unitary -/

/-- `Û^(1)_θ ∈ unitary`. -/
theorem spinHalfRot1_mem_unitary (θ : ℝ) :
    spinHalfRot1 θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · -- star Û * Û = 1 ↔ Û · Ûᴴ = 1 (mul_eq_one_comm in matrix), and Û · Ûᴴ = 1 by spinHalfRot1_unitary.
    rw [show star (spinHalfRot1 θ) = (spinHalfRot1 θ).conjTranspose from rfl,
      spinHalfRot1_adjoint]
    -- Now goal: Û_{-θ} * Û_θ = 1. Use group law Û_a · Û_b = Û_{a+b}.
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

/-! ## Forward Euler-angle parametrization -/

/-- The unitary 2×2 matrix built from three Euler angles `(φ, θ, ψ)`
via the standard Z–Y–Z decomposition: `Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ`.
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

end LatticeSystem.Quantum
