import LatticeSystem.Quantum.SpinS.BasisVecSBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# `basisSpinS`: the multi-site spin-`S` standard basis as a `Basis`

Bundles PR #917's `basisVecS_linearIndependent` and
`basisVecS_span_eq_top` into a mathlib `Basis` structure
`basisSpinS V N : Basis (V → Fin (N + 1)) ℂ ((V → Fin (N + 1)) → ℂ)`,
inheriting all standard `Basis` properties.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The multi-site spin-`S` standard basis: `basisVecS` packaged as
a mathlib `Module.Basis`. -/
noncomputable def basisSpinS (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) :
    Module.Basis (V → Fin (N + 1)) ℂ ((V → Fin (N + 1)) → ℂ) :=
  Module.Basis.mk basisVecS_linearIndependent
    (le_of_eq basisVecS_span_eq_top.symm)

/-- `basisSpinS V N σ = basisVecS σ`: the basis applied at index `σ`
returns the corresponding standard basis vector. -/
@[simp]
theorem basisSpinS_apply (σ : V → Fin (N + 1)) :
    basisSpinS V N σ = basisVecS σ := by
  unfold basisSpinS
  rw [Module.Basis.mk_apply]

end LatticeSystem.Quantum
