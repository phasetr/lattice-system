# lattice-system

A Lean 4 + Mathlib formalization project targeting general lattice models.

This project subsumes and generalizes the earlier
[ising-model](https://github.com/phasetr/ising-model) project, with the
following scope progressively covered.

## Scope

| Area | Stage | Typical references |
|---|---|---|
| Classical spin systems (Ising etc.) | Inherited from ising-model | Friedli-Velenik, Glimm-Jaffe |
| Quantum spin systems | Current focus | Tasaki, Bru-Pedra |
| Hubbard / BCS | Medium term | Tasaki 1998, Bru-Pedra, Kashima |
| CAR-algebraic formulation | Medium-long term | Araki-Moriya 2003, Bru-Pedra |
| Thermodynamic limit, phase transitions | Long term | Simon, Friedli-Velenik |
| Lattice QCD | Longest term | Aarts, Davies |

## Project status

Initial scaffolding. No theorems formalized yet.

- A survey of Mathlib's current support for quantum spin systems has been
  completed (kept locally in the author's planning notes).
- CI: Lean Action CI + docgen-action + Jekyll Pages.

## Documentation

- Project page: https://phasetr.github.io/lattice-system/
- API documentation (doc-gen4): https://phasetr.github.io/lattice-system/docs/

## Formalized theorems

None yet.

## Roadmap

| Phase | Scope | Status |
|---|---|---|
| P0 | Project skeleton, CI, documentation infrastructure | In progress |
| P1 | Finite-volume quantum spin systems (Pauli, Gibbs state) | Not started |
| P2 | Finite-volume Hubbard / BCS | Not started |
| P3 | CAR algebras, quasi-local C*-algebras, KMS states | Not started |
| P4 | Thermodynamic limit, phase transitions | Not started |
| P5 | Lattice QCD | Not started |

## Build

```
lake build
```

Uses Lean 4.29.1 (see `lean-toolchain`).
