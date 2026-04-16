/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Magnetization subspace `H_M` and direct sum decomposition
(Tasaki §2.2 eqs. (2.2.9)/(2.2.10))

The Hilbert space of a spin-1/2 system on lattice `Λ` decomposes as a
direct sum over total magnetization eigenvalues `M`:

```
H = ⊕_M H_M, where H_M := {|Φ⟩ : Ŝ_tot^(3) |Φ⟩ = M |Φ⟩}.
```

This module formalizes both pieces:

* `magnetizationSubspace M` — the eigenspace of `Ŝ_tot^(3)` for
  eigenvalue `M`, as a `Submodule ℂ ((Λ → Fin 2) → ℂ)`.
* `IsInMagnetizationSubspace M v` — the membership predicate (the
  underlying eigenvalue equation; kept as an alias for backwards
  compatibility with PR #16).
* `basisVec_mem_magnetizationSubspace` — every basis state lies in its
  magnetization sector (the carrier of Tasaki eq. (2.2.10)).
* `magnetizationSubspace_disjoint` — distinct sectors have trivial
  intersection.
* `iSup_magnetizationSubspace_eq_top` — every vector decomposes
  as a sum across sectors (because basisVec spans the full space and
  each basis state lies in some sector).
* `magnetizationSubspace_isInternal` — the family forms an internal
  direct sum (`DirectSum.IsInternal`).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-- The magnetization-`M` subspace `H_M`: the `Ŝ_tot^(3)`-eigenspace
for eigenvalue `M`, packaged as a `Submodule ℂ`. -/
noncomputable def magnetizationSubspace (M : ℂ) :
    Submodule ℂ ((Λ → Fin 2) → ℂ) where
  carrier := { v | (totalSpinHalfOp3 Λ).mulVec v = M • v }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.mulVec_zero, smul_zero]
  add_mem' := by
    intros v w hv hw
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [Matrix.mulVec_add, hv, hw, smul_add]
  smul_mem' := by
    intros c v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [Matrix.mulVec_smul, hv, smul_comm]

/-- A vector `v` lies in the magnetization-`M` subspace `H_M` iff it is
an eigenvector of `Ŝ_tot^(3)` with eigenvalue `M`. -/
def IsInMagnetizationSubspace (M : ℂ) (v : (Λ → Fin 2) → ℂ) : Prop :=
  (totalSpinHalfOp3 Λ).mulVec v = M • v

/-- Membership in `magnetizationSubspace` unfolds to the eigenvalue equation. -/
@[simp]
theorem mem_magnetizationSubspace_iff (M : ℂ) (v : (Λ → Fin 2) → ℂ) :
    v ∈ magnetizationSubspace Λ M ↔ (totalSpinHalfOp3 Λ).mulVec v = M • v :=
  Iff.rfl

/-- Bridge between the predicate (PR #16) and the `Submodule`-membership
form. -/
theorem isInMagnetizationSubspace_iff_mem (M : ℂ) (v : (Λ → Fin 2) → ℂ) :
    IsInMagnetizationSubspace Λ M v ↔ v ∈ magnetizationSubspace Λ M :=
  Iff.rfl

/-- Every computational-basis state `|σ⟩` lies in `H_{|σ|/2}`, i.e. it is
an eigenvector of `Ŝ_tot^(3)` with eigenvalue `|σ|/2` (Tasaki eq. (2.2.10),
predicate form). -/
theorem basisVec_isInMagnetizationSubspace (σ : Λ → Fin 2) :
    IsInMagnetizationSubspace Λ ((magnetization Λ σ : ℂ) / 2) (basisVec σ) :=
  totalSpinHalfOp3_mulVec_basisVec_eq_magnetization Λ σ

/-- `Submodule`-form of `basisVec_isInMagnetizationSubspace`. -/
theorem basisVec_mem_magnetizationSubspace (σ : Λ → Fin 2) :
    (basisVec σ : (Λ → Fin 2) → ℂ) ∈
      magnetizationSubspace Λ ((magnetization Λ σ : ℂ) / 2) :=
  basisVec_isInMagnetizationSubspace Λ σ

/-! ## Disjointness of distinct sectors -/

/-- Distinct magnetization eigenvalues give disjoint subspaces.
The proof uses that an eigenvector with two distinct eigenvalues
must be zero: `(M - M') • v = 0` and `M ≠ M'` force `v = 0`. -/
theorem magnetizationSubspace_disjoint {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (magnetizationSubspace Λ M) (magnetizationSubspace Λ M') := by
  rw [Submodule.disjoint_def]
  intros v hM hM'
  rw [mem_magnetizationSubspace_iff] at hM hM'
  -- Ŝ v = M v = M' v ⇒ (M - M') v = 0 ⇒ v = 0 (since M ≠ M').
  have heq : M • v = M' • v := hM.symm.trans hM'
  have hsub : (M - M') • v = 0 := by
    rw [sub_smul, heq, sub_self]
  have hne : M - M' ≠ 0 := sub_ne_zero.mpr hMM'
  exact (smul_eq_zero.mp hsub).resolve_left hne

/-! ## Spanning: every vector lies in the supremum of all sectors -/

/-- A vector expressed as a finite sum of basis states lies in the
supremum of all magnetization subspaces (each basis state lies in
its own sector, and the supremum is closed under sums). -/
private theorem sum_basisVec_mem_iSup
    (s : Finset (Λ → Fin 2)) (c : (Λ → Fin 2) → ℂ) :
    (∑ σ ∈ s, c σ • basisVec σ) ∈
      iSup (magnetizationSubspace Λ) := by
  refine Submodule.sum_mem _ ?_
  intros σ _
  refine Submodule.smul_mem _ _ ?_
  exact (le_iSup (magnetizationSubspace Λ) ((magnetization Λ σ : ℂ) / 2))
    (basisVec_mem_magnetizationSubspace Λ σ)

/-- Every vector decomposes as a finite sum over basis states (since
the index set `Λ → Fin 2` is finite). -/
private theorem eq_sum_basisVec (v : (Λ → Fin 2) → ℂ) :
    v = ∑ σ : Λ → Fin 2, v σ • basisVec σ := by
  funext τ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  rw [Finset.sum_eq_single τ]
  · simp
  · intros σ _ hστ
    rw [if_neg (Ne.symm hστ), mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The supremum of all magnetization subspaces is the full space:
every vector decomposes as a sum of basis states, and each basis state
lies in its own sector. -/
theorem iSup_magnetizationSubspace_eq_top :
    iSup (magnetizationSubspace Λ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [eq_sum_basisVec Λ v]
  exact sum_basisVec_mem_iSup Λ Finset.univ v

/-! ## Internal direct sum (`DirectSum.IsInternal`) -/

/-- The magnetization subspace coincides with the standard
`Module.End.eigenspace` of the total `Ŝ^(3)_tot` operator (viewed as
a `(Λ → Fin 2) → ℂ`-endomorphism via `Matrix.mulVecLin`). -/
theorem magnetizationSubspace_eq_eigenspace (M : ℂ) :
    magnetizationSubspace Λ M =
      Module.End.eigenspace ((totalSpinHalfOp3 Λ).mulVecLin) M := by
  ext v
  rw [mem_magnetizationSubspace_iff, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply]

/-- The magnetization subspaces form an `iSupIndep` family: distinct
eigenvalues give linearly independent eigenspaces. Inherited from
`Module.End.eigenspaces_iSupIndep`. -/
theorem magnetizationSubspace_iSupIndep :
    iSupIndep (magnetizationSubspace Λ) := by
  have heq : magnetizationSubspace Λ =
      Module.End.eigenspace ((totalSpinHalfOp3 Λ).mulVecLin) := by
    funext M
    exact magnetizationSubspace_eq_eigenspace Λ M
  rw [heq]
  exact Module.End.eigenspaces_iSupIndep _

/-- The magnetization subspaces form an internal direct sum. -/
theorem magnetizationSubspace_isInternal :
    DirectSum.IsInternal (magnetizationSubspace Λ) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨magnetizationSubspace_iSupIndep Λ,
     iSup_magnetizationSubspace_eq_top Λ⟩

end LatticeSystem.Quantum
