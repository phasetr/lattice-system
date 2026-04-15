# lattice-system

A Lean 4 + Mathlib formalization project targeting general lattice models.

This project subsumes and generalizes the earlier
[ising-model](https://github.com/phasetr/ising-model) project, with the
following scope progressively covered.

## Scope

| Area | Stage | Typical references |
|---|---|---|
| Classical spin systems (Ising etc.) | Inherited from ising-model | Friedli-Velenik, Glimm-Jaffe |
| Quantum spin systems | Current focus | Tasaki, Nielsen-Chuang (cross-check) |
| Hubbard / BCS | Medium term | Tasaki 1998, Bru-Pedra, Kashima |
| CAR-algebraic formulation | Medium-long term | Araki-Moriya 2003, Bru-Pedra |
| Thermodynamic limit, phase transitions | Long term | Simon, Friedli-Velenik |
| Lattice QCD | Longest term | Aarts, Davies |

## Project status

Initial formalization is under way. The current focus is finite-volume
quantum spin systems. A survey of Mathlib's support for this domain has
been completed (kept locally in the author's planning notes). A
Mathlib-style mathematical guide to the formalized code is maintained
in [`tex/proof-guide.tex`](tex/proof-guide.tex).

CI: Lean Action CI + docgen-action + Jekyll Pages.

## Documentation

- Project page: https://phasetr.github.io/lattice-system/
- API documentation (doc-gen4): https://phasetr.github.io/lattice-system/docs/
- Mathematical guide to the code: [`tex/proof-guide.tex`](tex/proof-guide.tex)

## Formalized theorems

All items below are formally proved with **zero `sorry`**. For the full
mathematical statement of each, see [`tex/proof-guide.tex`](tex/proof-guide.tex).

### Single-site Pauli operators (`LatticeSystem/Quantum/Pauli.lean`)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1, eq. (2.1.8), p. 15. Cross-checked with Nielsen-Chuang
*Quantum Computation and Quantum Information*, §2.1.3 Figure 2.2
(pp. 65-66) for the definitions, Ex. 2.19 (p. 70) for Hermiticity,
Ex. 2.41 (p. 78) for `(σ^α)² = I` and anticommutation, and Ex. 2.40
(p. 77) for the commutator (which, combined with the anticommutator,
gives the cyclic products).

| Lean name | Statement |
|---|---|
| `pauliX_isHermitian`, `pauliY_isHermitian`, `pauliZ_isHermitian` | `(σ^α)† = σ^α` for `α ∈ {x, y, z}` |
| `pauliX_mul_self`, `pauliY_mul_self`, `pauliZ_mul_self` | `(σ^α)² = I` |
| `pauliX_mul_pauliY`, `pauliY_mul_pauliZ`, `pauliZ_mul_pauliX` | `σ^x σ^y = i·σ^z`, cyclic |
| `pauliX_anticomm_pauliY`, `pauliY_anticomm_pauliZ`, `pauliZ_anticomm_pauliX` | `σ^α σ^β + σ^β σ^α = 0` for `α ≠ β` |

### Multi-body operator space and site embedding (`LatticeSystem/Quantum/ManyBody.lean`)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 "Quantum Spin Systems", pp. 21-26 (tensor-product
Hilbert space and site-local operators). `onSite i A` is the matrix
realization of `(⊗ₖ≠ᵢ I) ⊗ Aᵢ` in the computational basis.

| Lean name | Statement |
|---|---|
| `onSite i A` | definition: single-site `A` acting at site `i`, identity elsewhere |
| `onSite_isHermitian` | Hermiticity lifts from `A` to `onSite i A` |
| `onSite_mul_onSite_of_ne` | operators embedded at distinct sites commute |
| `Matrix.IsHermitian.mul_of_commute` | product of commuting Hermitian matrices is Hermitian |

### One-dimensional open-chain quantum Ising (`LatticeSystem/Quantum/IsingChain.lean`)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.3 "Quantum Ising Model", eq. (3.3.1) on p. 55
(one-dimensional transverse-field quantum Ising on an open chain).
Our `quantumIsingHamiltonian N J h` uses the Pauli convention
`σ = 2 · S` and introduces an explicit bond coupling `J`, so it agrees
with Tasaki's (3.3.1) up to these constants.

| Lean name | Statement |
|---|---|
| `quantumIsingHamiltonian N J h` | definition: `H = -J Σ σ^z_i σ^z_{i+1} - h Σ σ^x_i` on `N+1` sites |
| `quantumIsingHamiltonian_isHermitian` | `H` is Hermitian for real `J`, `h` |

## Roadmap

| Phase | Scope | Status |
|---|---|---|
| P0 | Project skeleton, CI, documentation infrastructure | Done |
| P1a | Finite-volume quantum spin operator algebra (Pauli, onSite, commutativity) | Done |
| P1b | Finite-chain quantum Ising Hamiltonian, Hermiticity | Done |
| P1c | Gibbs state `ρ = e^{-βH}/Z`, expectation `⟨O⟩_β = Tr(ρO)` | Not started |
| P1d | Periodic boundary conditions, other quantum chains (Heisenberg) | Not started |
| P2 | Finite-volume Hubbard / BCS | Not started |
| P3 | CAR algebras, quasi-local C*-algebras, KMS states | Not started |
| P4 | Thermodynamic limit, phase transitions | Not started |
| P5 | Lattice QCD | Not started |

## Build

```
lake build
```

Uses Lean 4.29.0 and Mathlib `v4.29.0` (see `lean-toolchain` and
`lakefile.toml`).
