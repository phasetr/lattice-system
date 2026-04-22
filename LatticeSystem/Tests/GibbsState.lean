/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.GibbsState

/-!
# Test coverage for Quantum/GibbsState

A+C+G+D coverage for the generic finite-dimensional Gibbs state
machinery `gibbsState β H`, `partitionFn`, `gibbsExpectation`, and
the β = 0 / Hermiticity / commute properties (refactor plan v4 §9
mapping table; refactor Phase 1 PR 7, #281).
-/

namespace LatticeSystem.Tests.GibbsState

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## D. signature shims for `gibbsState` Hermiticity -/

/-- `gibbsState β H` is Hermitian when `H` is. -/
example {H : ManyBodyOp Λ} (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState β H).IsHermitian :=
  gibbsState_isHermitian hH β

/-- `gibbsState β H` commutes with `H`. -/
example (β : ℝ) (H : ManyBodyOp Λ) : Commute (gibbsState β H) H :=
  gibbsState_commute_hamiltonian β H

/-! ## D: `partitionFn` β = 0 closed form -/

/-- `Z(0) = dim` (Tasaki §A: at β = 0, partition function = trace of
identity = dimension of Hilbert space). -/
example (H : ManyBodyOp Λ) :
    partitionFn (Λ := Λ) 0 H =
      (Fintype.card (Λ → Fin 2) : ℂ) :=
  partitionFn_zero H

/-- `Z(0) ≠ 0`. -/
example (H : ManyBodyOp Λ) : partitionFn (Λ := Λ) 0 H ≠ 0 :=
  partitionFn_zero_ne_zero H

/-! ## D: `gibbsExpectation` β = 0 / Hermitian observable / linearity -/

/-- `⟨A⟩_0 = Tr A / dim` (β = 0 closed form). -/
example (H A : ManyBodyOp Λ) :
    gibbsExpectation 0 H A =
      ((Fintype.card (Λ → Fin 2) : ℂ))⁻¹ * Matrix.trace A :=
  gibbsExpectation_zero H A

/-- `⟨O⟩_β.im = 0` for Hermitian `O` (real expectation value). -/
example {H O : ManyBodyOp Λ} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (β : ℝ) :
    (gibbsExpectation β H O).im = 0 :=
  gibbsExpectation_im_of_isHermitian hH hO β

/-! ## A. decide-based universal: small `Fin n` partition fn dim -/

/-- For `Λ = Fin 2`, `Z(0) = 2^2 = 4` (universally on H). -/
example (H : ManyBodyOp (Fin 2)) :
    partitionFn (Λ := Fin 2) 0 H = (4 : ℂ) := by
  rw [partitionFn_zero]
  norm_num

/-- For `Λ = Fin 3`, `Z(0) = 2^3 = 8`. -/
example (H : ManyBodyOp (Fin 3)) :
    partitionFn (Λ := Fin 3) 0 H = (8 : ℂ) := by
  rw [partitionFn_zero]
  norm_num

end LatticeSystem.Tests.GibbsState
