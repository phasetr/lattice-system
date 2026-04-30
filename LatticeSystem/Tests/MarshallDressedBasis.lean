/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallDressedBasis

/-!
# Test coverage for the Marshall-dressed standard basis
(Tasaki §2.5 eq. (2.5.8))
-/

namespace LatticeSystem.Tests.MarshallDressedBasis

open LatticeSystem.Quantum

/-! ## API smoke checks on `Fin 2` with sublattice indicator
`A = {0}` (the single A-site of a two-site bipartite graph). -/

/-- `marshallDressedBasis_self`: dressed value at own configuration
equals the Marshall sign. -/
example (σ : Fin 2 → Fin 2) :
    marshallDressedBasis (fun x : Fin 2 => decide (x = 0)) σ σ =
      marshallSignOf (fun x : Fin 2 => decide (x = 0)) σ :=
  marshallDressedBasis_self _ σ

/-- Off-diagonal value vanishes. -/
example (σ τ : Fin 2 → Fin 2) (h : τ ≠ σ) :
    marshallDressedBasis (fun x : Fin 2 => decide (x = 0)) σ τ = 0 :=
  marshallDressedBasis_of_ne _ h

/-- The Marshall sign squares to one on any vertex type with any
sublattice indicator. -/
example (σ : Fin 2 → Fin 2) :
    marshallSignOf (fun x : Fin 2 => decide (x = 0)) σ *
        marshallSignOf (fun x : Fin 2 => decide (x = 0)) σ = 1 :=
  marshallSignOf_sq_eq_one _ σ

/-- Orthonormality on `Fin 2` configurations under the real bilinear
pairing: diagonal = 1, off-diagonal = 0. -/
example :
    ∑ τ : Fin 2 → Fin 2,
        marshallDressedBasis (fun x : Fin 2 => decide (x = 0))
            (fun _ : Fin 2 => (0 : Fin 2)) τ *
          marshallDressedBasis (fun x : Fin 2 => decide (x = 0))
            (fun _ : Fin 2 => (0 : Fin 2)) τ = 1 := by
  rw [marshallDressedBasis_inner]
  simp

/-- Membership in `H_M`: the dressed basis lies in the magnetization
sector of the underlying configuration. -/
example (σ : Fin 2 → Fin 2) :
    marshallDressedBasis (fun x : Fin 2 => decide (x = 0)) σ ∈
      magnetizationSubspace (Fin 2) ((magnetization (Fin 2) σ : ℂ) / 2) :=
  marshallDressedBasis_mem_magnetizationSubspace _ σ

/-- Magnetization-zero configuration: the dressed basis lies in `H_0`. -/
example (σ : Fin 2 → Fin 2) (hσ : magnetization (Fin 2) σ = 0) :
    marshallDressedBasis (fun x : Fin 2 => decide (x = 0)) σ ∈
      magnetizationSubspace (Fin 2) (0 : ℂ) :=
  marshallDressedBasis_mem_magnetizationSubspace_zero _ hσ

end LatticeSystem.Tests.MarshallDressedBasis
