/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MagnetizationSubspace

/-!
# Test coverage for Quantum/MagnetizationSubspace

A+C+G+D coverage for `magnetizationSubspace`, `IsInMagnetizationSubspace`,
basisVec membership, sector orthogonality / direct-sum decomposition
(refactor plan v4 §9 mapping table; refactor Phase 1 PR 8, #281).
-/

namespace LatticeSystem.Tests.MagnetizationSubspace

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## D. signature shims -/

/-- `IsInMagnetizationSubspace` ↔ `magnetizationSubspace` membership. -/
example (M : ℂ) (v : (Λ → Fin 2) → ℂ) :
    v ∈ magnetizationSubspace Λ M ↔
      IsInMagnetizationSubspace Λ M v :=
  mem_magnetizationSubspace_iff Λ M v

/-- Basis vectors live in the sector matching their magnetisation. -/
example (σ : Λ → Fin 2) :
    basisVec σ ∈ magnetizationSubspace (Λ := Λ)
      ((magnetization Λ σ : ℂ) / 2) :=
  basisVec_mem_magnetizationSubspace Λ σ

/-- Distinct sectors are linearly disjoint. -/
example {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (magnetizationSubspace Λ M)
      (magnetizationSubspace Λ M') :=
  magnetizationSubspace_disjoint Λ hMM'

/-- Direct-sum decomposition: the sectors span the whole space. -/
example :
    iSup (magnetizationSubspace Λ) = ⊤ :=
  iSup_magnetizationSubspace_eq_top Λ

/-- The sectors are independent. -/
example : iSupIndep (magnetizationSubspace Λ) :=
  magnetizationSubspace_iSupIndep Λ

/-! ## A. decide-based universal: small `Fin 2 → Fin 2` magnetisation
catalog -/

/-- For every `σ : Fin 2 → Fin 2`, the magnetisation is in `{-2, 0, 2}`. -/
example :
    ∀ σ : Fin 2 → Fin 2,
        magnetization (Fin 2) σ = -2 ∨
          magnetization (Fin 2) σ = 0 ∨
          magnetization (Fin 2) σ = 2 := by
  decide

end LatticeSystem.Tests.MagnetizationSubspace
