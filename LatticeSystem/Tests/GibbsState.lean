/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.GibbsState
import LatticeSystem.Quantum.GibbsState.Covariance

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

/-! ## D. Covariance extension (`GibbsState/Covariance.lean`)

Codex audit Item 6: pin representative results from the
extension sub-file so the generic covariance / variance / im-
of-Hermitian / anticommutator-im / commutator-re companion
family is directly exercised at the generic layer (was previously
only indirectly covered through Heisenberg / Ising wrappers). -/

/-- Generic squared-observable expectation is real for Hermitian
`H, O`. -/
example {H O : ManyBodyOp Λ} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (β : ℝ) :
    (gibbsExpectation β H (O * O)).im = 0 :=
  gibbsExpectation_sq_im_of_isHermitian hH hO β

/-- Generic n-th-power observable expectation is real. -/
example {H O : ManyBodyOp Λ} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (β : ℝ) (n : ℕ) :
    (gibbsExpectation β H (O ^ n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian hH hO β n

/-- Generic Hamiltonian expectation `(⟨H⟩_β).im = 0` for Hermitian H. -/
example {H : ManyBodyOp Λ} (hH : H.IsHermitian) (β : ℝ) :
    (gibbsExpectation β H H).im = 0 :=
  gibbsExpectation_hamiltonian_im hH β

/-- Generic conservation law `⟨[H, A]⟩_β = 0`. -/
example (β : ℝ) (H A : ManyBodyOp Λ) :
    gibbsExpectation β H (H * A - A * H) = 0 :=
  gibbsExpectation_commutator_hamiltonian β H A

/-- Generic `⟨H · O⟩_β` real for Hermitian `H, O`. -/
example {H O : ManyBodyOp Λ} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (β : ℝ) :
    (gibbsExpectation β H (H * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im hH hO β

/-- Generic anticommutator `⟨A · B + B · A⟩_β` real for Hermitian
`H, A, B`. -/
example {H A B : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (β : ℝ) :
    (gibbsExpectation β H (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im hH hA hB β

/-- Generic commutator `⟨A · B − B · A⟩_β` purely imaginary
for Hermitian `H, A, B`. -/
example {H A B : ManyBodyOp Λ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (β : ℝ) :
    (gibbsExpectation β H (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re hH hA hB β

/-- Generic `partitionFn_im_of_isHermitian`. -/
example {H : ManyBodyOp Λ} (hH : H.IsHermitian) (β : ℝ) :
    (partitionFn β H).im = 0 :=
  partitionFn_im_of_isHermitian hH β

/-- Generic `gibbsState_pow_trace`: `Tr(ρ_β^n) = Z(nβ)/Z(β)^n`. -/
example (β : ℝ) (H : ManyBodyOp Λ) (n : ℕ) :
    ((gibbsState β H) ^ n).trace
      = partitionFn ((n : ℝ) * β) H / (partitionFn β H) ^ n :=
  gibbsState_pow_trace β H n

end LatticeSystem.Tests.GibbsState
