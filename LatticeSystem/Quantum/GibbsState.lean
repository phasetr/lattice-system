/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Gibbs state for finite-volume quantum systems

Following Tasaki *Physics and Mathematics of Quantum Many-Body Systems*,
§3.3, this module defines the finite-volume quantum Gibbs state

  `ρ_β = exp(-β H) / Z`,   `Z = Tr(exp(-β H))`,

for a Hermitian Hamiltonian `H : ManyBodyOp Λ` and inverse temperature
`β : ℝ`. We prove:

* `gibbsExp_isHermitian` — `exp(-β H)` is Hermitian.
* `gibbsState_trace` — `Tr(ρ_β) = 1` (given `Z ≠ 0`).
* `gibbsState_isHermitian` — `ρ_β` is Hermitian.
* `gibbsExpectation_one` — `⟨1⟩_β = 1` (given `Z ≠ 0`).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Negation of a real cast to `ℂ` is self-adjoint. -/
private lemma negReal_isSelfAdjoint (β : ℝ) : IsSelfAdjoint (-(β : ℂ)) := by
  rw [IsSelfAdjoint, star_neg, RCLike.star_def, Complex.conj_ofReal]

/-! ## Gibbs exponential -/

/-- The Gibbs exponential `exp(-β H)` for inverse temperature `β : ℝ`
and Hamiltonian `H : ManyBodyOp Λ`. -/
noncomputable def gibbsExp (β : ℝ) (H : ManyBodyOp Λ) : ManyBodyOp Λ :=
  NormedSpace.exp ((-(β : ℂ)) • H)

/-- `exp(-β H)` is Hermitian when `H` is Hermitian. -/
theorem gibbsExp_isHermitian {H : ManyBodyOp Λ} (hH : H.IsHermitian) (β : ℝ) :
    (gibbsExp β H).IsHermitian := by
  exact Matrix.IsHermitian.exp (hH.smul (negReal_isSelfAdjoint β))

/-! ## Partition function -/

/-- The partition function `Z(β) = Tr(exp(-β H))`. -/
noncomputable def partitionFn (β : ℝ) (H : ManyBodyOp Λ) : ℂ :=
  (gibbsExp β H).trace

/-! ## Gibbs state (density matrix)

Note: `partitionFn β H ≠ 0` (the partition function is nonzero) is
NOT proved here because the CFC-based proof
(`IsSelfAdjoint.exp_nonneg` under `open scoped MatrixOrder` +
`PosSemidef.trace_eq_zero_iff` + `Matrix.isUnit_exp`) causes
deterministic timeout in Lean's typeclass resolution. All downstream
theorems take `hZ : partitionFn β H ≠ 0` as an explicit hypothesis. -/

/-- The Gibbs state (density matrix) `ρ_β = (1/Z) exp(-β H)`. -/
noncomputable def gibbsState (β : ℝ) (H : ManyBodyOp Λ) : ManyBodyOp Λ :=
  (1 / partitionFn β H) • gibbsExp β H

/-- The Gibbs state has unit trace: `Tr(ρ_β) = 1`. -/
theorem gibbsState_trace {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) :
    (gibbsState β H).trace = 1 := by
  simp only [gibbsState, Matrix.trace_smul, smul_eq_mul, one_div]
  exact inv_mul_cancel₀ hZ

/-- The Gibbs state is Hermitian. -/
theorem gibbsState_isHermitian {H : ManyBodyOp Λ} (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState β H).IsHermitian := by
  apply Matrix.IsHermitian.smul (gibbsExp_isHermitian hH β)
  have htr : star (partitionFn β H) = partitionFn β H := by
    simp only [partitionFn, ← Matrix.trace_conjTranspose, (gibbsExp_isHermitian hH β).eq]
  rw [IsSelfAdjoint, one_div, star_inv₀, htr]

/-! ## Expectation value -/

/-- The Gibbs expectation value `⟨O⟩_β = Tr(ρ_β O)`. -/
noncomputable def gibbsExpectation (β : ℝ) (H O : ManyBodyOp Λ) : ℂ :=
  ((gibbsState β H) * O).trace

/-- `⟨1⟩_β = 1`. -/
theorem gibbsExpectation_one {H : ManyBodyOp Λ} (β : ℝ)
    (hZ : partitionFn β H ≠ 0) :
    gibbsExpectation β H 1 = 1 := by
  simp only [gibbsExpectation, mul_one]
  exact gibbsState_trace β hZ

end LatticeSystem.Quantum
