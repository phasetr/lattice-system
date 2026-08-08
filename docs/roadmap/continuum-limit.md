---
layout: page
title: "Continuum-limit roadmap"
permalink: /continuum-limit-roadmap/
---

# Continuum-limit historical design scaffold

> This page preserves an earlier Phase A–D design scaffold. It is not the current work queue; tracking Issues and their mirrors govern current implementation.

<!-- legacy-source:start:2732:2779 -->
## Continuum-limit roadmap

The project's long-term goals include the `φ^4` / Ising continuum
limit and lattice-QCD-style formalisations, both of which are defined
as limits `a → 0` of families of finite-spacing lattice systems. A
survey of the gap between the current finite-volume matrix framework
and what the continuum limit actually demands was recorded during
Phase A scoping (consulted codex twice on scope and design choices)
and proposes the four phases below.

**Phase A (historical scaffold; implementation recorded at the time)**. Add a **thin type-level tag**
`class LatticeWithSpacing (Λ : Type*) where spacing : ℝ≥0`
so that a lattice spacing `a : ℝ≥0` can be attached to `Λ` as
metadata. Provide the default instance `Fin (N + 1)` with
`spacing := 1` so every pre-existing Hamiltonian in the library is
`rfl`-equivalent to its `spacing := 1` specialisation. No geometry,
no rescaling, no continuum object.

**Phase B (deferred)**. Lattice sequences `Λ_n` with
`spacing a_n → 0`, rescaling of coupling constants
(`J_n = ĥ · a_n^{-2+d}` etc.), and lattice-point embeddings in
`ℝ^d`. Introduce when a concrete theorem (e.g. Osterwalder-Schrader,
a specific block-spin transformation) requires iterating over a
spacing sequence.

**Phase C (deferred)**. Operator-valued distribution / GNS /
Hilbert-space infrastructure to house the continuum limit itself.
Per codex (2026-04-22), we do **not** generalise
`ManyBodyOp Λ = Matrix _ _ ℂ` to a type class preemptively: existing
proofs depend on Matrix-specific API (`conjTranspose`, `exp`,
`trace`, `mulVec`, entry formulas), and the right abstraction becomes
clear only once a second concrete backend (infinite-volume Hilbert
space, quasi-local C*-algebra) is in place.

**Phase D (deferred)**. Coupling-constant running
`g : ℝ≥0 → ℝ` and renormalisation-group transformations. Follows
phases B-C.

| Lean name | Statement | File |
|---|---|---|
| `LatticeWithSpacing` | `class LatticeWithSpacing (Λ : Type*) where spacing : ℝ≥0` — thin type-level tag recording the lattice spacing `a : ℝ≥0` of a vertex type | `Lattice/Scale.lean` |
| `spacingOf` | `spacingOf Λ := LatticeWithSpacing.spacing` — named accessor | `Lattice/Scale.lean` |
| `instLatticeWithSpacingFinSucc` | default `spacing := 1` instance for `Fin (N + 1)`, making every existing Hamiltonian `rfl`-equivalent to the unit-spacing specialisation | `Lattice/Scale.lean` |
| `spacing_fin_succ` / `spacingOf_fin_succ` | `spacing = 1` computed at `Fin (N + 1)` | `Lattice/Scale.lean` |
| `instLatticeWithSpacingInt` | default `spacing := 1` instance for `ℤ` (infinite chain — matches `integerChainGraph`) | `Lattice/Scale.lean` |
| `instLatticeWithSpacingIntSq` | default `spacing := 1` instance for `ℤ × ℤ` (infinite 2D square lattice — matches `integerSquareLatticeGraph`) | `Lattice/Scale.lean` |
| `spacing_int` / `spacingOf_int` / `spacing_int_sq` / `spacingOf_int_sq` | `spacing = 1` computed at `ℤ`, `ℤ × ℤ` | `Lattice/Scale.lean` |

<!-- legacy-source:end:2732:2779 -->
