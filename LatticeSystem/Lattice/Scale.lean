/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.NNReal.Basic

/-!
# Lattice spacing as a type-level tag (Phase A of the continuum-limit plan)

The project's long-term goals include the `φ^4` / Ising continuum
limit and lattice-QCD-style formalisations. Both require a notion of
**lattice spacing** `a > 0`, and both ultimately describe the
continuum as the limit `a → 0` of a family of finite-spacing lattice
systems.

At the current formal level every Hamiltonian is indexed by an
abstract vertex type `Λ`, and `a` plays no formal role — all existing
work corresponds to the `a = 1` instance. This module introduces a
**thin type-level tag** recording `a` as metadata on `Λ`, without
altering any existing definition:

* `LatticeWithSpacing Λ` is a one-field type class providing
  `LatticeWithSpacing.spacing : ℝ≥0`.
* `Fin (N + 1)` is given the default instance `spacing := 1` so every
  pre-existing Hamiltonian (chains, rings, Hubbard, Ising, Heisenberg)
  is `rfl`-equivalent to the `spacing := 1` specialisation.

No geometric embedding (lattice points in `ℝ^d`), no coupling
rescaling, no lattice sequence, and no continuum-limit target object
is defined here. Those are phases B-D of the
[Continuum-limit roadmap](https://phasetr.github.io/lattice-system/#continuum-limit-roadmap)
in `docs/index.md`, and will be introduced only when a concrete
theorem needs them.

The separation follows the codex consultation (2026-04-22): add
spacing as *metadata* now, keep geometry separate, and do **not**
generalise `ManyBodyOp Λ = Matrix ...` to a type class until a
second concrete backend is needed.
-/

namespace LatticeSystem.Lattice

open NNReal

/-- `LatticeWithSpacing Λ` equips a vertex type `Λ` with a lattice
spacing `a : ℝ≥0` as a type-level tag.

This is a thin, purely metadata-carrying class: no existing
definition in the library consumes it, and the default instance for
`Fin (N + 1)` below uses `spacing := 1`, so the current library is
`rfl`-equivalent to its `LatticeWithSpacing`-tagged specialisation.

The class exists so that future work on the continuum limit
(`a → 0`, cf. the
[Continuum-limit roadmap](https://phasetr.github.io/lattice-system/#continuum-limit-roadmap))
has a type-level handle on `a`: rescaling of coupling constants,
lattice sequences `a_n → 0`, and renormalisation-group
transformations will all be expressed in terms of `spacing`. -/
class LatticeWithSpacing (Λ : Type*) : Type where
  /-- The lattice spacing `a : ℝ≥0` attached to `Λ`. -/
  spacing : ℝ≥0

/-- Convenience accessor: `spacingOf Λ` is the lattice spacing of a
`[LatticeWithSpacing Λ]`-tagged vertex type. -/
@[simp] def spacingOf (Λ : Type*) [inst : LatticeWithSpacing Λ] : ℝ≥0 :=
  inst.spacing

/-- Default `spacing := 1` instance for finite chains `Fin (N + 1)`.

With this instance every existing Hamiltonian in the library — built
on `Fin (N + 1)` for the 1D chain, `Fin (2N + 2)` for the spinful
Hubbard chain, etc. — corresponds to the unit-spacing specialisation
of the `LatticeWithSpacing` tag, without any change to existing
definitions or proofs. -/
instance instLatticeWithSpacingFinSucc (N : ℕ) :
    LatticeWithSpacing (Fin (N + 1)) where
  spacing := 1

@[simp] lemma spacing_fin_succ (N : ℕ) :
    LatticeWithSpacing.spacing (Λ := Fin (N + 1)) = 1 := rfl

@[simp] lemma spacingOf_fin_succ (N : ℕ) :
    spacingOf (Fin (N + 1)) = 1 := rfl

/-- Default `spacing := 1` instance for `ℤ`, the infinite chain.

This is the unit-spacing specialisation of the infinite-volume
setting that future continuum-limit / thermodynamic-limit work will
inhabit (`integerChainGraph` lives on `ℤ`). Anisotropic / non-unit
spacings on `ℤ` will be introduced via a named local instance when a
specific theorem requires them — the default here just keeps the
library `rfl`-equivalent to the existing unit-spacing conventions. -/
instance instLatticeWithSpacingInt : LatticeWithSpacing ℤ where
  spacing := 1

@[simp] lemma spacing_int :
    LatticeWithSpacing.spacing (Λ := ℤ) = 1 := rfl

@[simp] lemma spacingOf_int : spacingOf ℤ = 1 := rfl

/-- Default `spacing := 1` instance for `ℤ × ℤ`, the infinite 2D
square lattice. Matches the 2D `integerSquareLatticeGraph` already
in the library. -/
instance instLatticeWithSpacingIntSq : LatticeWithSpacing (ℤ × ℤ) where
  spacing := 1

@[simp] lemma spacing_int_sq :
    LatticeWithSpacing.spacing (Λ := ℤ × ℤ) = 1 := rfl

@[simp] lemma spacingOf_int_sq : spacingOf (ℤ × ℤ) = 1 := rfl

end LatticeSystem.Lattice
