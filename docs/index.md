---
layout: default
title: Home
---

## lattice-system

A Lean 4 + Mathlib formalization project targeting general lattice models.
This project subsumes and generalizes the earlier
[ising-model](https://github.com/phasetr/ising-model) project, progressively
covering classical spin systems, quantum spin systems, Hubbard, BCS,
CAR algebras, and eventually lattice QCD.

## Scope

| Area | Stage | Typical references |
|---|---|---|
| Classical spin systems | Inherited from ising-model | Friedli-Velenik, Glimm-Jaffe |
| Quantum spin systems | Current focus | Tasaki, Nielsen-Chuang (cross-check) |
| Hubbard / BCS | Medium term | Tasaki 1998, Bru-Pedra |
| CAR-algebraic formulation | Medium-long term | Araki-Moriya, Bru-Pedra |
| Thermodynamic limit | Long term | Simon, Friedli-Velenik |
| Lattice QCD | Longest term | Aarts, Davies |

## Formalized theorems

All items below are formally proved with **zero `sorry`**. Full
mathematical statements and proof sketches are in
[`tex/proof-guide.tex`](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex).

### Single-site Pauli operators

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*; cross-checked with Nielsen-Chuang §2.1.3.

| Lean name | Statement | File |
|---|---|---|
| `pauliX/Y/Z_isHermitian` | `(σ^α)† = σ^α` | `Quantum/Pauli.lean` |
| `pauliX/Y/Z_mul_self` | `(σ^α)² = I` | `Quantum/Pauli.lean` |
| `pauliX_mul_pauliY` etc. | `σ^x σ^y = i·σ^z` (cyclic) | `Quantum/Pauli.lean` |
| `pauliX_anticomm_pauliY` etc. | `σ^α σ^β + σ^β σ^α = 0` (α ≠ β) | `Quantum/Pauli.lean` |

### Multi-body operator space

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, chapter on spin chains.

| Lean name | Statement | File |
|---|---|---|
| `onSite i A` | site-embedded operator | `Quantum/ManyBody.lean` |
| `onSite_isHermitian` | `A.IsHermitian → (onSite i A).IsHermitian` | `Quantum/ManyBody.lean` |
| `onSite_mul_onSite_of_ne` | operators at distinct sites commute | `Quantum/ManyBody.lean` |
| `Matrix.IsHermitian.mul_of_commute` | commuting Hermitians multiply Hermitian | `Quantum/ManyBody.lean` |

### One-dimensional open-chain quantum Ising

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, chapter on spin chains.

| Lean name | Statement | File |
|---|---|---|
| `quantumIsingHamiltonian N J h` | `H = -J Σ σ^z_i σ^z_{i+1} - h Σ σ^x_i` | `Quantum/IsingChain.lean` |
| `quantumIsingHamiltonian_isHermitian` | `H` is Hermitian for real `J`, `h` | `Quantum/IsingChain.lean` |

## Links

- [API documentation (doc-gen4)](docs/)
- [GitHub repository](https://github.com/phasetr/lattice-system)
- [Mathematical guide (`tex/proof-guide.tex`)](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex)
- [ising-model (upstream project)](https://github.com/phasetr/ising-model)
