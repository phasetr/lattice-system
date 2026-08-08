---
layout: page
title: "Legacy landing-page content"
permalink: /history/legacy-landing-content/
---

# Legacy landing-page content

> Historical snapshot moved from the former monolithic index. It is not a current status ledger.

<!-- legacy-source:start:6:71 -->
## lattice-system

A Lean 4 + Mathlib formalization project targeting general lattice models.
This project subsumes and generalizes the earlier
[ising-model](https://github.com/phasetr/ising-model) project, progressively
covering classical spin systems, quantum spin systems, Hubbard, BCS,
CAR algebras, and eventually lattice QCD.

## Design axis: graphs, not lattices

Despite the name, the **primary combinatorial abstraction in this
library is a graph `(Λ, E_Λ)`** — finite for finite-volume work and
infinite for the thermodynamic-limit / algebraic-formulation work
that is a major long-term goal — not "a lattice". Concrete lattices
(the 1D chain, square / cubic grids, infinite chains, ℤ^d, …) appear
only as specific instances such as `SimpleGraph.pathGraph`,
`SimpleGraph.cycleGraph`, products of these, or their infinite
analogues. This convention follows the standard mathematical-physics
literature on many-body systems on graphs (Lieb's theorem on
bipartite lattices, the Marshall–Lieb–Mattis theorem, Miyao 2021
§3, …) and aligns the project with mathlib's `SimpleGraph`
foundations.

Finite-volume work uses `Λ : Type*` together with `[Fintype Λ]`
when needed (e.g. for traces, partition functions, finite sums of
local terms); infinite-volume work drops the `Fintype` assumption
and uses graphs over types like `ℤ` or `ℤ^d` instead.

The bridge from a `SimpleGraph` to the pairwise coupling
`J : Λ → Λ → ℂ` consumed by `heisenbergHamiltonian` (and similar
operators) lives in `LatticeSystem.Lattice.Graph` (`couplingOf`).
Existing chain coupling families (`openChainCoupling`,
`periodicChainCoupling`) are characterised as
`couplingOf (pathGraph _) _` and `couplingOf (cycleGraph _) _`
respectively.

## Scope

| Area | Stage | Typical references |
|---|---|---|
| Classical spin systems | Inherited from ising-model | Friedli-Velenik, Glimm-Jaffe |
| Quantum spin systems | Current focus | Tasaki, Nielsen-Chuang (cross-check) |
| Hubbard / BCS | Medium term | Tasaki 1998, Bru-Pedra |
| CAR-algebraic formulation | Medium-long term | Araki-Moriya, Bru-Pedra |
| Thermodynamic limit (infinite graphs) | Long term, **major project goal** | Simon, Friedli-Velenik, Bratteli-Robinson |
| Lattice QCD | Longest term | Aarts, Davies |

## Refactoring conventions and review criteria

A **single-source-of-truth document** for refactoring conventions
applied as the review checklist on every pull request:
[Refactoring conventions and review criteria](/lattice-system/refactoring-conventions/).
Topics: test methods (decide / bridge / small-exhaustive / shim /
`#guard_msgs`), module-split criteria, generic / dedup conventions,
deprecation window policy, naming / docstring rules, linter
exceptions, public-doc synchronisation.

The companion page [Deprecation window](/lattice-system/deprecations/) tracks
currently-deprecated public declarations, the `since` date,
recommended replacement, and earliest-removal window.

The companion page
[Jordan–Wigner façade module overview](/lattice-system/jordan-wigner-overview/)
gives the per-sub-file overview table for the
`LatticeSystem/Fermion/JordanWigner/` re-export hub.

<!-- legacy-source:end:6:71 -->
