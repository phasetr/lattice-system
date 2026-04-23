/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Lattice.Scale

/-!
# Test coverage for the `LatticeWithSpacing` type-level tag

Regression tests for Phase A of the continuum-limit preparation
plan (see the [Continuum-limit roadmap](https://phasetr.github.io/lattice-system/#continuum-limit-roadmap)
section of the project page). These `example` blocks pin down:

1. the default `spacing := 1` instance on `Fin (N + 1)`,
2. the two `@[simp]`-accessor equations, and
3. that the `spacingOf` helper reduces definitionally to the class
   field.
-/

namespace LatticeSystem.Tests.Scale

open LatticeSystem.Lattice NNReal

/-! ## Default instance values -/

example : LatticeWithSpacing.spacing (Λ := Fin 1) = 1 := rfl
example : LatticeWithSpacing.spacing (Λ := Fin 2) = 1 := rfl
example : LatticeWithSpacing.spacing (Λ := Fin 3) = 1 := rfl
example (N : ℕ) :
    LatticeWithSpacing.spacing (Λ := Fin (N + 1)) = 1 := rfl

/-! ## `spacingOf` accessor -/

example : spacingOf (Fin 1) = 1 := rfl
example : spacingOf (Fin 2) = 1 := rfl
example (N : ℕ) : spacingOf (Fin (N + 1)) = 1 := rfl

/-! ## Named-lemma checks -/

example (N : ℕ) :
    LatticeWithSpacing.spacing (Λ := Fin (N + 1)) = 1 :=
  spacing_fin_succ N

example (N : ℕ) : spacingOf (Fin (N + 1)) = 1 :=
  spacingOf_fin_succ N

/-! ## Custom spacing instance (sanity check that the class admits
values other than `1`).

This example uses a local `letI` to synthesise an alternative
instance, verifying that the class is genuinely parametric in
`spacing : ℝ≥0`. Nothing in the library depends on this
construction; it is purely a type-system sanity check. -/

example :
    letI : LatticeWithSpacing (Fin 4) := ⟨(2 : ℝ≥0)⟩
    LatticeWithSpacing.spacing (Λ := Fin 4) = (2 : ℝ≥0) := rfl

/-! ## Infinite-volume instances -/

example : LatticeWithSpacing.spacing (Λ := ℤ) = 1 := rfl
example : spacingOf ℤ = 1 := rfl
example : LatticeWithSpacing.spacing (Λ := ℤ × ℤ) = 1 := rfl
example : spacingOf (ℤ × ℤ) = 1 := rfl

example : LatticeWithSpacing.spacing (Λ := ℤ) = 1 := spacing_int
example : spacingOf ℤ = 1 := spacingOf_int
example : LatticeWithSpacing.spacing (Λ := ℤ × ℤ) = 1 := spacing_int_sq
example : spacingOf (ℤ × ℤ) = 1 := spacingOf_int_sq

/-! ## Custom spacing for ℤ (anisotropic continuum-limit scaffold) -/

example :
    letI : LatticeWithSpacing ℤ := ⟨(1 / 2 : ℝ≥0)⟩
    LatticeWithSpacing.spacing (Λ := ℤ) = (1 / 2 : ℝ≥0) := rfl

end LatticeSystem.Tests.Scale
