/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin

/-!
# Magnetization subspace `H_M` (Tasaki §2.2 eqs. (2.2.9)/(2.2.10))

The Hilbert space of a spin-1/2 system on lattice `Λ` decomposes as a
direct sum over total magnetization eigenvalues `M`:

```
H = ⊕_M H_M, where H_M := {|Φ⟩ : Ŝ_tot^(3) |Φ⟩ = M |Φ⟩}.
```

This module defines the membership predicate for `H_M` (as a Prop on
vectors), and proves that every computational-basis state `basisVec σ`
lies in `H_{|σ|/2}`.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-- A vector `v` lies in the magnetization-`M` subspace `H_M` iff it is an
eigenvector of `Ŝ_tot^(3)` with eigenvalue `M`. -/
def IsInMagnetizationSubspace (M : ℂ) (v : (Λ → Fin 2) → ℂ) : Prop :=
  (totalSpinHalfOp3 Λ).mulVec v = M • v

/-- Every computational-basis state `|σ⟩` lies in `H_{|σ|/2}`, i.e. it is
an eigenvector of `Ŝ_tot^(3)` with eigenvalue `|σ|/2` (Tasaki eq. (2.2.10)). -/
theorem basisVec_mem_magnetizationSubspace (σ : Λ → Fin 2) :
    IsInMagnetizationSubspace Λ ((magnetization Λ σ : ℂ) / 2) (basisVec σ) := by
  unfold IsInMagnetizationSubspace
  exact totalSpinHalfOp3_mulVec_basisVec_eq_magnetization Λ σ

end LatticeSystem.Quantum
