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

## Roadmap

| Phase | Scope | Status |
|---|---|---|
| P0 | Project skeleton, CI, documentation infrastructure | Done |
| P1a | Finite-volume quantum spin operator algebra (Pauli, `onSite`, commutativity) | Done |
| P1b | Finite-chain quantum Ising Hamiltonian, Hermiticity, Gibbs state instantiation (Hermiticity, commutativity with `H`, β = 0 closed form, expectation realness for Hermitian observables, conservation `⟨[H, A]⟩ = 0`, energy expectation as bond + transverse-field decomposition, energy expectation real, `⟨H · O⟩` real for Hermitian `O`, `⟨H^n⟩` real for any `n : ℕ`) | Done |
| P1c (Tasaki §2.1) | Spin-1/2 operators `Ŝ^(α)` and the commutator algebra | Done |
| P1d (Tasaki §2.1) | Basis states `|ψ^↑⟩, |ψ^↓⟩`, raising/lowering `Ŝ^±` (S = 1/2) | Done |
| P1d' (Tasaki §2.1) | S = 1 matrix representations (eq. (2.1.9)) | Done |
| P1d'' (Tasaki §2.1) | Problem 2.1.a for S = 1/2 (Pauli basis of `M_2(ℂ)`) | Done |
| P1d''' (Tasaki §2.1) | Problem 2.1.a for `S ≥ 1` (polynomial basis of `M_{2S+1}(ℂ)` via Lagrange interpolation in `Ŝ^(3)` and `Ŝ^±` ladder action) | Done for `S = 1`; general `S ≥ 1` (`Fin (2S+1)` abstraction) deferred — see [open items](#open-items--axioms) |
| P1e (Tasaki §2.1) | S = 1/2 rotation `Û^(α)_θ` closed form, `Û_0`, adjoint, `Û_{2π}` | Done |
| P1e' | Rotation group law and unitarity | Done |
| P1e'' (Tasaki §2.1) | `Û^(α)_θ = exp(-iθŜ^(α))` via `Matrix.exp_diagonal` + `Matrix.exp_conj` (Problem 2.1.b, all 3 axes) | Done |
| P1e''' (Tasaki §2.1) | π-rotations: `Û^(α)_π = -2i·Ŝ^(α)`, anticommutation at distinct axes | Done |
| P1e'''' (Tasaki §2.1) | `Û^(α)_π · Û^(β)_π = Û^(γ)_π`; conjugations `(Û^(α)_π)†·Ŝ^(β)·Û^(α)_π = ±Ŝ^(β)` | Done |
| P1e''''' (Tasaki §2.1) | General θ transformation `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) - sin θ · ε^{αβγ} Ŝ^(γ)` (eq. (2.1.16)) | Done |
| P1e'''''' (Tasaki §2.1) | Z₂ × Z₂ representation (eqs. (2.1.27)-(2.1.34)): S = 1/2 projective + S = 1 genuine | Done |
| P1d-S1 (Tasaki §2.1) | S = 1 basis states and `Ŝ^(3)`, `Ŝ^±` actions (eqs. (2.1.2)–(2.1.6) for S = 1) | Done |
| P1f (Tasaki §2.2) | Abstract lattice `Λ`, site operators `Ŝ_x^(α)`, distinct-site commutation (eq. (2.2.6), `x ≠ y`) | Done |
| P1f-same (Tasaki §2.2) | Same-site commutation `[Ŝ_x^(α), Ŝ_x^(β)] = i·ε^{αβγ} Ŝ_x^(γ)` (eq. (2.2.6), `x = y`) | Done |
| P1f' (Tasaki §2.2) | Total spin operator `Ŝ_tot^(α)` (eq. (2.2.7)) and Hermiticity | Done |
| P1f'-pm (Tasaki §2.2) | Total raising/lowering `Ŝ^±_tot = Σ_x Ŝ_x^±` (eq. (2.2.8)) | Done |
| P1f-mag (Tasaki §2.2) | Total magnetization `|σ| := Σ_x spinSign(σ_x)` (eq. (2.2.2)) | Done |
| P1f'' (Tasaki §2.2) | Global rotation `Û^(α)_θ = exp(-iθ Ŝ_tot^(α))` (eq. (2.2.11)) | Done (proved without axioms) |
| P1f''' (Tasaki §2.2) | SU(2) / U(1) invariance (eqs. (2.2.12)-(2.2.13)) | Done (commutativity `totalSpinHalfRot{α}_commute_of_commute`, unitarity `totalSpinHalfRot{α}_conjTranspose_mul_self`, and finite-form invariance `totalSpinHalfRot{α}_conj_eq_self_of_commute` all proved without axioms) |
| P1f'''' (Tasaki §2.2) | Two-site inner product `Ŝ_x · Ŝ_y` raising/lowering decomposition (eq. (2.2.16)) | Done |
| P1f''''' (Tasaki §2.2) | SU(2) invariance of `Ŝ_x · Ŝ_y` and eigenvalues (eqs. (2.2.17)–(2.2.19)) | Done |
| P1f-2c (Tasaki §2.2 Problem 2.2.c) | SU(2)-averaged two-site state = singlet projector (eq. (2.2.15)); integration over Euler angles `φ ∈ [0,2π]`, `θ ∈ [0,π]` | Done |
| P1i (Tasaki §2.4) | Heisenberg Hamiltonian on the fully-polarised state: `H |s…s⟩ = (∑_{x,y} J(x,y)·(if x=y then 3/4 else 1/4)) · |s…s⟩` (eq. (2.4.5), `S = 1/2`); plus the ladder step `Ŝ_tot^± · |s…s⟩` preserves the same H-eigenvalue (eqs. (2.4.7)/(2.4.9), `S = 1/2`) and its iterated form `(Ŝ_tot^±)^k · |s…s⟩` for every `k : ℕ`; plus `[H, Û^(α)_θ] = 0` for the global rotation (eq. (2.4.7) operator-level), the single-axis rotated constant-spin state `Û^(α)_θ · |s…s⟩` shares the H-eigenvalue, and the two-axis spin-coherent state `Û^(3)_ϕ Û^(2)_θ · |s…s⟩ = |Ξ_θ,ϕ⟩` (eq. (2.4.6) for `s = 0`); plus the magnetic-quantum-number labelling `Ŝtot^(3) · (Ŝtot^-)^k · |↑..↑⟩ = (Smax - k) · (Ŝtot^-)^k · |↑..↑⟩` (eq. (2.4.9), unnormalised, lowering from highest weight) and its dual `Ŝtot^(3) · (Ŝtot^+)^k · |↓..↓⟩ = (-Smax + k) · (Ŝtot^+)^k · |↓..↓⟩` (eq. (2.4.9), unnormalised, raising from lowest weight); plus the Casimir invariance `Ŝtot² · (Ŝtot^∓)^k · |s..s⟩ = Smax(Smax+1) · (Ŝtot^∓)^k · |s..s⟩` for any constant `s`. For the matched highest/lowest-weight ladders, the unnormalised iterates `(Ŝtot^-)^k · |↑..↑⟩` and `(Ŝtot^+)^k · |↓..↓⟩` carry `(H, Ŝtot², Ŝtot^(3))` simultaneous eigenvalues `(c_J, Smax(Smax+1), Smax∓k)`; plus the boundary annihilations `Ŝtot^- · |↓..↓⟩ = 0` and `Ŝtot^+ · |↑..↑⟩ = 0` ensuring the ladder terminates after spanning all `2Smax + 1 = |Λ| + 1` magnetisation sectors — building toward the full |Φ_M⟩ / |Ξ_θ,ϕ⟩ ferromagnetic ground-state space | Done |
| P1g | Gibbs state `ρ = e^{-βH}/Z`, `Tr(ρ) = 1`, `⟨1⟩ = 1`, `Z(0) = dim`, `Z(0) ≠ 0`, linearity `⟨O₁+O₂⟩ = ⟨O₁⟩+⟨O₂⟩`, `⟨c·O⟩ = c·⟨O⟩`, `⟨-O⟩ = -⟨O⟩`, `⟨A−B⟩ = ⟨A⟩−⟨B⟩`, `⟨Σ f⟩ = Σ ⟨f⟩`, `[ρ, H] = 0`, reality of `⟨O⟩` for Hermitian `O`, conservation `⟨[H,A]⟩ = 0`, anticommutator real / commutator imaginary, `(⟨H·O⟩).im = 0`, β = 0 closed form `ρ_0 = I/dim` and `⟨A⟩_0 = Tr A / dim`, one-parameter group property `e^{-(β₁+β₂)H} = e^{-β₁H} · e^{-β₂H}` and invertibility, exact discrete semigroup identity `e^{-(nβ)H} = (e^{-βH})^n` (extended to `n : ℤ` via `gibbsExp_inv`) | Done |
| P1h | Periodic boundary conditions, Heisenberg chain (open and periodic BC), Gibbs state instantiation for both BCs (Hermiticity, commutativity with `H`, β = 0 closed form, expectation realness for Hermitian observables, conservation `⟨[H, A]⟩ = 0`, energy expectation as a bond-sum decomposition, energy expectation real, `⟨H · O⟩` real for Hermitian `O`, `⟨H^n⟩` real for any `n : ℕ`) | Done |
| P2 | Finite-volume Hubbard / BCS | In progress (single-mode CAR algebra; multi-mode Jordan–Wigner backbone: JW string + multi-mode `c_i`, `c_i†` definitions and Hermiticity, `c_0` reductions, full on-site CAR `c_i² = 0`, `(c_i†)² = 0`, `{c_i, c_i†} = 1`, adjoint `(c_i)ᴴ = c_i†`, JW string idempotent `J² = 1`, site-occupation number operator `n_i` with Hermiticity and idempotency) |
| P3 | CAR algebras, quasi-local C*-algebras, KMS states | Not started |
| P4 | Thermodynamic limit, phase transitions | Not started |
| P5 | Lattice QCD | Not started |

## Formalized theorems

All items below are formally proved with **zero `sorry`**. Full
mathematical statements and proof sketches are in
[`tex/proof-guide.tex`](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex).

### Single-site Pauli operators

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.8), p. 15. Cross-checked with Nielsen-Chuang
§2.1.3 Figure 2.2 (pp. 65-66, definitions), Ex. 2.19 (p. 70,
Hermiticity), Ex. 2.41 (p. 78, `(σ^α)² = I` and anticommutation),
Ex. 2.40 (p. 77, commutator, whence the cyclic products).

| Lean name | Statement | File |
|---|---|---|
| `pauliX/Y/Z_isHermitian` | `(σ^α)† = σ^α` | `Quantum/Pauli.lean` |
| `pauliX/Y/Z_mul_self` | `(σ^α)² = I` | `Quantum/Pauli.lean` |
| `pauliX_mul_pauliY` etc. | `σ^x σ^y = i·σ^z` (cyclic) | `Quantum/Pauli.lean` |
| `pauliX_anticomm_pauliY` etc. | `σ^α σ^β + σ^β σ^α = 0` (α ≠ β) | `Quantum/Pauli.lean` |

### Spin-1/2 operators (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.1), (2.1.7), (2.1.8), pp. 13-15.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfOp1/2/3` | `Ŝ^(α) := σ^(α) / 2` (Tasaki (2.1.7)) | `Quantum/SpinHalf.lean` |
| `pauliX_eq_two_smul_spinHalfOp1` etc. | `σ^(α) = 2 · Ŝ^(α)` (Tasaki (2.1.8)) | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_isHermitian` etc. | `Ŝ^(α)` is Hermitian | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_mul_self` etc. | `(Ŝ^(α))² = (1/4) · I` | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_anticomm_spinHalfOp2` etc. | anticommutation at `α ≠ β` | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_commutator_spinHalfOp2` etc. | `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` (Tasaki (2.1.1)) | `Quantum/SpinHalf.lean` |
| `spinHalf_total_spin_squared` | `Σ (Ŝ^(α))² = (3/4) · I`, i.e. `S(S+1)` with `S=1/2` | `Quantum/SpinHalf.lean` |

### Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.26), p. 17 (closed form) and eq. (2.1.23),
p. 16 (`Û_{2π} = -1` for half-odd-integer spin).

| Lean name | Statement | File |
|---|---|---|
| `spinHalfRot1/2/3` | `Û^(α)_θ := cos(θ/2) · 1 - 2i · sin(θ/2) · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_zero` | `Û^(α)_0 = 1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_adjoint` | `(Û^(α)_θ)† = Û^(α)_{-θ}` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_two_pi` | `Û^(α)_{2π} = -1` (Tasaki eq. (2.1.23)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_mul` | group law `Û^(α)_θ · Û^(α)_φ = Û^(α)_{θ+φ}` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_unitary` | unitarity `Û^(α)_θ · (Û^(α)_θ)† = 1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi` | `Û^(α)_π = -2i · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi_sq` | `(Û^(α)_π)² = -1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_pi_anticomm_spinHalfRot2_pi` (and cyclic) | `{Û^(α)_π, Û^(β)_π} = 0` for `α ≠ β` (Tasaki (2.1.25)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi_conjTranspose` | `(Û^(α)_π)† = 2i · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_pi_mul_spinHalfRot2_pi` (and cyclic) | `Û^(α)_π · Û^(β)_π = Û^(γ)_π` (Tasaki (2.1.29), S=1/2) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi_conj_spinHalfOp_*` | axis invariance and sign flip at θ=π (Tasaki (2.1.15)/(2.1.21)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{2,3,1}` | `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) - sin θ · Ŝ^(γ)` (Tasaki eq. (2.1.16), even-ε cyclic triple) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{3,1,2}` | `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) + sin θ · Ŝ^(γ)` (Tasaki eq. (2.1.16), odd-ε triple) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{1,2,3}` | same-axis invariance `(Û^(α)_θ)† Ŝ^(α) Û^(α)_θ = Ŝ^(α)` (Tasaki eq. (2.1.15)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_half_pi_conj_spinHalfOp_*` | `π/2`-rotation conjugation `(Û^(α)_{π/2})† Ŝ^(β) Û^(α)_{π/2} = -ε^{αβγ} Ŝ^(γ)` (Tasaki eq. (2.1.22), 6 cases) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot3_eq_exp` | `Û^(3)_θ = exp(-iθ Ŝ^(3))` via `Matrix.exp_diagonal` + Euler (Problem 2.1.b, axis 3) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp` | `Û^(3)_φ Û^(2)_θ |ψ^↑⟩ = e^{-iφ/2} cos(θ/2) |ψ^↑⟩ + e^{iφ/2} sin(θ/2) |ψ^↓⟩` (coherent state, Problem 2.1.d) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown` | `Û^(3)_φ Û^(2)_θ |ψ^↓⟩ = -e^{-iφ/2} sin(θ/2) |ψ^↑⟩ + e^{iφ/2} cos(θ/2) |ψ^↓⟩` (rotation of spin-down, Problem 2.2.c auxiliary) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot3_half_pi_mul_spinHalfRot2_half_pi_mulVec_spinHalfUp` | specialization at θ = φ = π/2 (Problem 2.1.e) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfDotVec` / `spinHalfDotVec_isHermitian` | vector inner product `Ŝ · v := Σ_α v_α Ŝ^(α)` and its Hermiticity (cf. (2.1.19)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot3_commute_spinHalfOp3_smul` | same-axis rotation commutes with `v · Ŝ^(3)` (cf. (2.1.20) along axis) | `Quantum/SpinHalfRotation.lean` |
| `hadamard` / `hadamard_mul_self` | the Hadamard basis-change matrix `W = (1/√2)·!![1,1;1,-1]` and `W·W = 1` | `Quantum/SpinHalfRotation.lean` |
| `hadamard_mul_spinHalfOp1_mul_hadamard` | `W · Ŝ^(1) · W = Ŝ^(3)` (basis change between σ^x and σ^z) | `Quantum/SpinHalfRotation.lean` |
| `hadamard_mul_spinHalfOp3_mul_hadamard` | `W · Ŝ^(3) · W = Ŝ^(1)` (inverse basis change) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_eq_hadamard_conj` | `Û^(1)_θ = W · Û^(3)_θ · W` (axis 1 rotation as Hadamard conjugate of axis 3) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_eq_exp` | `Û^(1)_θ = exp(-iθ Ŝ^(1))` via Hadamard conjugation + `Matrix.exp_conj` (Problem 2.1.b, axis 1) | `Quantum/SpinHalfRotation.lean` |
| `yDiag` / `yDiagAdj` / `yDiag_mul_yDiagAdj` / `yDiag_mul_spinHalfOp3_mul_yDiagAdj` | y-axis basis-change unitary `V` with `V·V† = 1` and `V·Ŝ^(3)·V† = Ŝ^(2)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot2_eq_yDiag_conj` / `spinHalfRot2_eq_exp` | `Û^(2)_θ = V·Û^(3)_θ·V†` and `Û^(2)_θ = exp(-iθ Ŝ^(2))` (Problem 2.1.b, axis 2) | `Quantum/SpinHalfRotation.lean` |

### 3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11))

| Lean name | Statement | File |
|---|---|---|
| `rot3D{1,2,3} θ` | 3×3 real rotation matrices by angle θ about each axis | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}_zero` | `R^(α)_0 = 1` | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}_pi` | `R^(α)_π` from general formula matches explicit π-rotation | `Quantum/Rotation3D.lean` |

### Z₂ × Z₂ representation (Tasaki §2.1 eqs. (2.1.27)-(2.1.34))

The Z₂ × Z₂ structure is proved across files:
- S = 1/2 (projective, eq. (2.1.31)): `spinHalfRot*_pi_sq = -1`, anticommutation, products.
- S = 1 (genuine, eq. (2.1.27)): `spinOnePiRot*_sq = 1`, commutation.

See `Quantum/Z2Z2.lean` for the unified documentation.

### 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.27)-(2.1.28), p. 18 and Problem 2.1.f.

| Lean name | Statement | File |
|---|---|---|
| `rot3D{1,2,3}Pi` | 3×3 real orthogonal π-rotation matrices | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}Pi_sq` | `(R^(α)_π)² = 1` | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}Pi_mul_rot3D{2,3,1}Pi` | `R^(α)_π · R^(β)_π = R^(γ)_π` (cyclic, Problem 2.1.f) | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}Pi_comm_*` | distinct-axis `R^(α)_π` and `R^(β)_π` commute | `Quantum/Rotation3D.lean` |

### Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a, p. 15.

| Lean name | Statement | File |
|---|---|---|
| `pauliCoeff0/1/2/3` | explicit coefficient functions | `Quantum/SpinHalfDecomp.lean` |
| `pauli_decomposition` | `A = Σᵢ cᵢ · σ^(i)` | `Quantum/SpinHalfDecomp.lean` |
| `spinHalf_decomposition` | same via `Ŝ^(α) = σ^(α) / 2` | `Quantum/SpinHalfDecomp.lean` |
| `pauli_linearIndep` | `{1, σ^x, σ^y, σ^z}` is linearly independent | `Quantum/SpinHalfDecomp.lean` |

### Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, §2.1 Problem 2.1.a, p. 15 + solution S.1, p. 493.

| Lean name | Statement | File |
|---|---|---|
| `spinOneProj{Plus,Zero,Minus}` | the three diagonal projectors `\|ψ^σ⟩⟨ψ^σ\|` (σ ∈ {+1, 0, -1}) | `Quantum/SpinOneDecomp.lean` |
| `spinOneProj{Plus,Zero,Minus}_eq_polynomial` | each diagonal projector equals a polynomial in `Ŝ^(3)` (Lagrange interpolation) | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit{01,02,10,12,20,21}` | the six off-diagonal matrix units `\|ψ^τ⟩⟨ψ^σ\|` (τ ≠ σ) | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit{01,12}_eq_polynomial` | `(1/√2) Ŝ^- · P_σ` for the two single-step lowering units | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit{10,21}_eq_polynomial` | `(1/√2) Ŝ^+ · P_σ` for the two single-step raising units | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit02_eq_polynomial` | `(1/2) (Ŝ^-)² · P_+` for the double-step lowering unit | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit20_eq_polynomial` | `(1/2) (Ŝ^+)² · P_-` for the double-step raising unit | `Quantum/SpinOneDecomp.lean` |
| `spinOne_decomposition` | every 3×3 complex matrix is a linear combination of the 9 matrix units (entry-wise); combined with the polynomial expressions above this gives Tasaki Problem 2.1.a for `S = 1` | `Quantum/SpinOneDecomp.lean` |

### S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.9), p. 15.

| Lean name | Statement | File |
|---|---|---|
| `spinOneOp1/2/3` | 3×3 matrix definitions (Tasaki (2.1.9)) | `Quantum/SpinOne.lean` |
| `spinOneOp1/2/3_isHermitian` | Hermiticity | `Quantum/SpinOne.lean` |
| `spinOneOp1_commutator_spinOneOp2` etc. | `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` (S = 1) | `Quantum/SpinOne.lean` |
| `spinOne_total_spin_squared` | `Σ (Ŝ^(α))² = 2 · I`, i.e. `S(S+1)` with `S = 1` | `Quantum/SpinOne.lean` |

### Basis states and raising/lowering (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.4), (2.1.5), (2.1.6), p. 14.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfUp`, `spinHalfDown` | `\|ψ^↑⟩`, `\|ψ^↓⟩` as column vectors (Tasaki (2.1.6)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOp3_mulVec_spinHalfUp/Down` | `Ŝ^(3)` eigenvalue equations (Tasaki (2.1.4)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus`, `spinHalfOpMinus` | raising/lowering `Ŝ^±` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus_eq_add`, `spinHalfOpMinus_eq_sub` | `Ŝ^± = Ŝ^(1) ± i · Ŝ^(2)` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus/Minus_mulVec_spinHalfUp/Down` | raising/lowering actions (Tasaki (2.1.5)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus/Minus_conjTranspose` | `(Ŝ^±)† = Ŝ^∓` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus_commutator_spinHalfOpMinus` | `[Ŝ^+, Ŝ^-] = 2 · Ŝ^(3)` | `Quantum/SpinHalfBasis.lean` |

### Basis states and raising/lowering for S = 1 (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.2), (2.1.3), (2.1.6), p. 14 for the `S = 1`
case (`σ ∈ {-1, 0, +1}`).

| Lean name | Statement | File |
|---|---|---|
| `spinOnePlus/Zero/Minus` | column vectors `|ψ^{+1}⟩, |ψ^{0}⟩, |ψ^{-1}⟩` | `Quantum/SpinOneBasis.lean` |
| `spinOneOp3_mulVec_spinOnePlus/Zero/Minus` | `Ŝ^(3)` eigenvalue equations (Tasaki (2.1.2), S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus`, `spinOneOpMinus` | 3×3 raising/lowering `Ŝ^±` for S = 1 | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus/Minus_mulVec_*` | raising/lowering actions `Ŝ^± |ψ^σ⟩ = √(2 - σ(σ±1)) |ψ^{σ±1}⟩` (Tasaki (2.1.3), S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus/Minus_conjTranspose` | `(Ŝ^±)† = Ŝ^∓` for S = 1 | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}` | S = 1 π-rotation matrices `û_α` (Tasaki eq. (2.1.33)) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot3_eq` | `û_3 = 1 - 2·(Ŝ^(3))²` (Tasaki eq. (2.1.32), α = 3 case) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}_sq` | `(û_α)² = 1` for integer S (Tasaki eq. (2.1.31) integer case) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}_comm_*` | distinct-axis commutation `û_α · û_β = û_β · û_α` for integer S | `Quantum/SpinOneBasis.lean` |
| `spinOneRot{1,2,3}` | `Û^(α)_θ = 1 - i sin θ · Ŝ^(α) - (1 - cos θ) · (Ŝ^(α))²` (Tasaki Problem 2.1.c, all 3 axes) | `Quantum/SpinOneBasis.lean` |
| `spinOneRot{1,2,3}_zero` / `spinOneRot{1,2,3}_pi` | boundary checks `Û^(α)_0 = 1` and `Û^(α)_π = û_α` | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2}_eq` | `û_α = 1 - 2·(Ŝ^(α))²` for axes 1, 2 (Tasaki eq. (2.1.30) for S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOp{1,2}_mul_self` | `(Ŝ^(α))²` explicit form (helper for the `_pi` boundary checks) | `Quantum/SpinOne.lean` |
| `spinOneOpPlus_eq_add`, `spinOneOpMinus_eq_sub` | `Ŝ^± = Ŝ^(1) ± i·Ŝ^(2)` for `S = 1` (Tasaki eq. (2.1.5), spin-1 case). Together with `spinOneUnit*_eq_polynomial` and `spinOneProj{Plus,Zero,Minus}_eq_polynomial`, fully reduces every off-diagonal matrix unit to a polynomial in `Ŝ^(1), Ŝ^(2), Ŝ^(3)` | `Quantum/SpinOneBasis.lean` |
| `spinHalfRot{1,2,3}_det_eq_one` | `det Û^(α)_θ = cos²(θ/2) + sin²(θ/2) = 1` (Pythagorean identity, complex form) | `Quantum/SpinHalfRotation.lean` |
| `SU2` | the special unitary submonoid `{ U | unitary U ∧ det U = 1 }` of `Matrix (Fin 2) (Fin 2) ℂ` | `Quantum/SU2.lean` |
| `spinHalfRot{1,2,3}_mem_unitary` | each axis rotation `Û^(α)_θ` lies in the unitary submonoid | `Quantum/SU2.lean` |
| `spinHalfRot{1,2,3}_mem_SU2` | each axis rotation `Û^(α)_θ` lies in `SU(2)` | `Quantum/SU2.lean` |
| `spinHalfEulerProduct φ θ ψ` | `Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ` — the forward Euler-angle parametrization | `Quantum/SU2.lean` |
| `spinHalfEulerProduct_mem_SU2` | the Euler-angle product lies in `SU(2)` | `Quantum/SU2.lean` |
| `integral_cos_zero_two_pi` | `∫ φ in 0..2π, cos φ = 0` (trig integral for Problem 2.2.c) | `Quantum/SU2Integral.lean` |
| `integral_sin_zero_two_pi` | `∫ φ in 0..2π, sin φ = 0` | `Quantum/SU2Integral.lean` |
| `integral_sin_zero_pi` | `∫ θ in 0..π, sin θ = 2` | `Quantum/SU2Integral.lean` |
| `integral_sin_two_pi_pi` | `∫ φ in 0..2π, ∫ θ in 0..π, sin θ = 4π` (SU(2) volume in Euler coordinates) | `Quantum/SU2Integral.lean` |
| `integral_sin_mul_cos_zero_pi` | `∫ θ in 0..π, sin θ · cos θ = 0` (antiderivative `sin²/2` via FTC) | `Quantum/SU2Integral.lean` |
| `integral_sin_mul_cos_sq_half_zero_pi` | `∫ θ in 0..π, sin θ · cos²(θ/2) = 1` (half-angle identity → `integral_sin` + `integral_sin_mul_cos`) | `Quantum/SU2Integral.lean` |
| `integral_sin_mul_sin_sq_half_zero_pi` | `∫ θ in 0..π, sin θ · sin²(θ/2) = 1` (same technique) | `Quantum/SU2Integral.lean` |
| `integral_cexp_I_mul_zero_two_pi` | `∫ φ in 0..2π, e^{iφ} dφ = 0` (complex trig integral for Problem 2.2.c) | `Quantum/SU2Integral.lean` |
| `integral_cexp_neg_I_mul_zero_two_pi` | `∫ φ in 0..2π, e^{-iφ} dφ = 0` (conjugate of the above) | `Quantum/SU2Integral.lean` |
| `totalRot32_two_site` | for `Λ = Fin 2`, the Euler-angle rotation `Û^(3)_φ Û^(2)_θ` of the two-site system factors as `onSite 0 (Û^(3)_φ Û^(2)_θ) * onSite 1 (Û^(3)_φ Û^(2)_θ)` (Problem 2.2.c auxiliary) | `Quantum/SU2Integral.lean` |
| `onSite_zero_mul_one_mulVec_basisVec` | explicit tensor-product action `(onSite 0 A * onSite 1 B) |σ⟩ = (A (σ 0)) ⊗ (B (σ 1))` on a two-site basis vector (Problem 2.2.c auxiliary) | `Quantum/SU2Integral.lean` |
| `problem_2_2_c` | **Main theorem** (Tasaki §2.2 eq. (2.2.15)): `(1/4π) ∫₀^{2π} dφ ∫₀^π dθ sin θ · Û^(3)_φ Û^(2)_θ ρ (Û^(3)_φ Û^(2)_θ)† = (1/2) P_singlet` where `ρ = \|↑₁↓₂⟩⟨↑₁↓₂\|`. The SU(2)-averaged two-site state equals one-half times the singlet projector. | `Quantum/SU2Integral.lean` |
| `spinOnePiRot{1,2,3}_mulVec_spinOne{Plus,Zero,Minus}` | π-rotation matrix elements on the basis `|ψ^{+1,0,-1}⟩` (Tasaki eq. (2.1.34) / Problem 2.1.g for S = 1) | `Quantum/SpinOneBasis.lean` |

### Multi-body operator space (abstract lattice)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2, pp. 21-26 (tensor-product Hilbert space and site-local
operators). The lattice `Λ` is an arbitrary finite set with decidable
equality; specializing to `Λ = Fin N` recovers an `N`-site chain.

| Lean name | Statement | File |
|---|---|---|
| `ManyBodyOp Λ` | `Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ` | `Quantum/ManyBody.lean` |
| `onSite i A` | site-embedded operator at `i : Λ` | `Quantum/ManyBody.lean` |
| `onSite_isHermitian` | `A.IsHermitian → (onSite i A).IsHermitian` | `Quantum/ManyBody.lean` |
| `onSite_add`, `onSite_sub`, `onSite_zero`, `onSite_smul`, `onSite_one` | linearity of the site embedding and `onSite i 1 = 1` | `Quantum/ManyBody.lean` |
| `onSite_mul_onSite_of_ne` | distinct-site commutation (Tasaki (2.2.6), `x ≠ y`, S = 1/2) | `Quantum/ManyBody.lean` |
| `basisVec` / `onSite_mulVec_basisVec` | tensor-product basis states and their action under site operators (Tasaki (2.2.1)/(2.2.4)) | `Quantum/ManyBody.lean` |
| `onSite_mul_onSite_same` | same-site product `onSite i A · onSite i B = onSite i (A · B)` (Tasaki (2.2.6), `x = y`) | `Quantum/ManyBody.lean` |
| `onSite_commutator_same` | same-site commutator `[onSite i A, onSite i B] = onSite i [A, B]` | `Quantum/ManyBody.lean` |
| `Matrix.IsHermitian.mul_of_commute` | commuting Hermitians multiply Hermitian | `Quantum/ManyBody.lean` |

### Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 eqs. (2.2.7) and (2.2.8), p. 22.

| Lean name | Statement | File |
|---|---|---|
| `totalSpinHalfOp1/2/3 Λ` | `Ŝ_tot^(α) := Σ_{x ∈ Λ} onSite x Ŝ^(α)` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp1/2/3_isHermitian` | `Ŝ_tot^(α)` is Hermitian | `Quantum/TotalSpin.lean` |
| `spinHalfOp_onSite_comm_of_ne` | S = 1/2 named wrapper of `onSite_mul_onSite_of_ne` | `Quantum/TotalSpin.lean` |
| `spinHalfOp{1,2,3}_onSite_commutator_spinHalfOp{2,3,1}_onSite` | same-site commutator `[Ŝ_x^(α), Ŝ_x^(β)] = i · Ŝ_x^(γ)` (Tasaki (2.2.6), `x = y`) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus`, `totalSpinHalfOpMinus` | `Ŝ^±_tot := Σ_{x ∈ Λ} onSite x Ŝ^±` (Tasaki (2.2.8)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_eq_add`, `totalSpinHalfOpMinus_eq_sub` | `Ŝ^±_tot = Ŝ^(1)_tot ± i · Ŝ^(2)_tot` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus/Minus_conjTranspose` | `(Ŝ^±_tot)† = Ŝ^∓_tot` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{1,2,3}_commutator_totalSpinHalfOp{2,3,1}` | `[Ŝ_tot^(α), Ŝ_tot^(β)] = i · Ŝ_tot^(γ)` (total spin commutation) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_commutator_totalSpinHalfOpPlus/Minus` | `[Ŝ_tot^(3), Ŝ^±_tot] = ±Ŝ^±_tot` (Cartan ladder relations) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared` / `_isHermitian` | Casimir operator `(Ŝ_tot)² := Σ_α (Ŝ_tot^(α))²` and its Hermiticity | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared_commutator_totalSpinHalfOp{1,2,3}` | `[(Ŝ_tot)², Ŝ_tot^(α)] = 0` (Casimir invariance, cf. Tasaki (2.2.12)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared_commutator_totalSpinHalfOpPlus/Minus` | `[(Ŝ_tot)², Ŝ^±_tot] = 0` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_commutator_totalSpinHalfOpMinus` | `[Ŝ^+_tot, Ŝ^-_tot] = 2 · Ŝ_tot^(3)` | `Quantum/TotalSpin.lean` |
| `magnetization`, `spinSign` | total magnetization `|σ| := Σ_x spinSign(σ_x)` (Tasaki (2.2.2)) | `Quantum/TotalSpin.lean` |
| `spinHalfSign` | half-integer eigenvalue of `Ŝ^(3)` on `Fin 2` basis | `Quantum/TotalSpin.lean` |
| `onSite_spinHalfOp3_mulVec_basisVec` | `Ŝ_x^(3) · |σ⟩ = ±(1/2) · |σ⟩` (single-site eigenvalue) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_basisVec` | `Ŝ_tot^(3) · |σ⟩ = (Σ_x spinHalfSign(σ_x)) · |σ⟩`, partial (2.2.10) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_basisVec_eq_magnetization` | `Ŝ_tot^(3) · |σ⟩ = (|σ| / 2) · |σ⟩` (full Tasaki eq. (2.2.10)) | `Quantum/TotalSpin.lean` |
| `onSite_spinHalfOpPlus/Minus_mulVec_basisVec` | raising/lowering action `Ŝ_x^± · |σ⟩` on a basis state at site `x` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus/Minus_mulVec_basisVec` | total `Ŝ^±_tot · |σ⟩` as a sum of site-wise actions | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}Pi` | global π-rotation `Û^(α)_π_tot := ∏_x Û^(α)_π_x` (Tasaki eq. (2.2.11) at θ = π) via `Finset.noncommProd` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3} θ` | general-θ global rotation `Û^(α)_θ_tot := ∏_x Û^(α)_θ_x` (Tasaki eq. (2.2.11)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}_zero` | `Û^(α)_0_tot = 1` (identity rotation) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}Pi_eq` | π-rotation matches the general-θ form at `θ = π` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}Pi_mul_totalSpinHalfRot{2,3,1}Pi` | `Û^(α)_π_tot · Û^(β)_π_tot = Û^(γ)_π_tot` (cyclic, Tasaki Problem 2.2.a) | `Quantum/TotalSpin.lean` |
| `onSiteRingHom x` / `onSiteLinearMap x` / `continuous_onSite x` | `onSite x` packaged as a `RingHom`, ℂ-linear map, and continuous function | `Quantum/TotalSpin.lean` |
| `onSite_pow` | `(onSite x A)^k = onSite x (A^k)` (powers commute with `onSite`) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}Pi_two_site` | for `Λ = Fin 2`, the global π-rotation factors as `onSite 0 (Û^(α)_π) * onSite 1 (Û^(α)_π)` (Tasaki Problem 2.2.b) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up` | for any `k : ℕ`, `Ŝtot^(3) · (Ŝtot^-)^k · |↑..↑⟩ = (|Λ|/2 - k) · (Ŝtot^-)^k · |↑..↑⟩` — the magnetic-quantum-number `M = Smax - k` labelling of the unnormalised iterates `(Ŝtot^-)^k · |Φ↑⟩` (Tasaki's `|Φ_M⟩` of eq. (2.4.9), p. 33, up to normalisation). Proof via Nat induction using the Cartan ladder `[Ŝtot^(3), Ŝtot^-] = -Ŝtot^-` | `Quantum/TotalSpin.lean` |
| `mulVec_preserves_eigenvalue_of_commute` | generic abstract pattern: for any `A B : ManyBodyOp Λ` with `Commute A B`, if `A · v = λ · v` then `A · (B · v) = λ · (B · v)` — the backbone of all commutator-based eigenvalue propagation | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down` | dual ladder: for any `k : ℕ`, `Ŝtot^(3) · (Ŝtot^+)^k · |↓..↓⟩ = (-|Λ|/2 + k) · (Ŝtot^+)^k · |↓..↓⟩` — same Tasaki §2.4 (2.4.9) ladder parameterised from the lowest weight `M = -Smax`, raised by `Ŝtot^+`. Proof: Nat induction using `[Ŝtot^(3), Ŝtot^+] = +Ŝtot^+` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_basisVec_const` / `_all_up` / `_all_down` | constant-config Ŝtot^(3) eigenvalue: `Ŝtot^(3) · |s..s⟩ = (|Λ| · spinHalfSign s) · |s..s⟩`; `s = 0` gives eigenvalue `|Λ|/2 = Smax`, `s = 1` gives `-|Λ|/2 = -Smax` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpMinus_mulVec_basisVec_all_down` | `Ŝtot^- · |↓..↓⟩ = 0`: lowering annihilates the bottom of the ladder | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_mulVec_basisVec_all_up` | `Ŝtot^+ · |↑..↑⟩ = 0`: raising annihilates the top of the ladder | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{Minus,Plus}_pow_basisVec_all_{up,down}_mem_magnetizationSubspace` | Submodule-form: `(Ŝtot^-)^k · |↑..↑⟩ ∈ H_{Smax - k}` and `(Ŝtot^+)^k · |↓..↓⟩ ∈ H_{-Smax + k}` — Tasaki §2.4 eq. (2.4.9) ladder iterates explicitly placed in the magnetisation sectors of Tasaki eq. (2.2.10) | `Quantum/MagnetizationSubspace.lean` |
| `basisVec_{upDown,basisSwap_upDown}_mem_magnetizationSubspace_zero` | two-site antiparallel states `|↑↓⟩`, `|↓↑⟩` lie in `H_0` (Tasaki §2.5 (2.5.2), p. 37, Néel state for the spin-1/2 Fin 2 instance) | `Quantum/MagnetizationSubspace.lean` |
| `singlet_mem_magnetizationSubspace_zero` / `triplet_zero_mem_magnetizationSubspace_zero` | singlet `|↑↓⟩ - |↓↑⟩` and triplet-`m=0` state `|↑↓⟩ + |↓↑⟩` lie in `H_0` (Tasaki §A.3 decomposition at the `M = 0` sector) | `Quantum/MagnetizationSubspace.lean` |
| `mulVec_mem_magnetizationSubspace_of_commute_of_mem` | generic preservation: any operator `A` with `Commute A (Ŝtot^(3))` maps each magnetisation sector `H_M` to itself — operator-level form of Tasaki §2.2 (2.2.10), p. 22 block-diagonalisation | `Quantum/MagnetizationSubspace.lean` |
| `totalSpinHalfSquared_mulVec_mem_magnetizationSubspace_of_mem` | Casimir specialisation: `Ŝtot²` preserves every `H_M` (since `[Ŝtot², Ŝtot^(3)] = 0`) | `Quantum/MagnetizationSubspace.lean` |
| `heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem` | for any `J : Λ → Λ → ℂ` and `M : ℂ`, `v ∈ H_M` implies `H · v ∈ H_M` — the operator-level statement that any Heisenberg Hamiltonian block-diagonalises against Tasaki §2.2 (2.2.10), p. 22 magnetisation-sector decomposition (consequence of SU(2) invariance `[H, Ŝtot^(3)] = 0`) | `Quantum/MagnetizationSubspace.lean` |
| `totalSpinHalfOpMinus_mulVec_mem_magnetizationSubspace_of_mem` | for any `M : ℂ`, `v ∈ H_M` implies `Ŝtot^- · v ∈ H_{M-1}` — the standard SU(2) lowering ladder action via the Cartan relation `[Ŝtot^(3), Ŝtot^-] = -Ŝtot^-` | `Quantum/MagnetizationSubspace.lean` |
| `totalSpinHalfOpPlus_mulVec_mem_magnetizationSubspace_of_mem` | for any `M : ℂ`, `v ∈ H_M` implies `Ŝtot^+ · v ∈ H_{M+1}` — the SU(2) raising ladder action via `[Ŝtot^(3), Ŝtot^+] = +Ŝtot^+` | `Quantum/MagnetizationSubspace.lean` |
| `totalSpinHalfRot{1,2,3}_two_site` | for `Λ = Fin 2` and any `θ`, the global rotation factors as `onSite 0 (Û^(α)_θ) * onSite 1 (Û^(α)_θ)` (general-θ extension of Problem 2.2.b) | `Quantum/TotalSpin.lean` |
| `onSite_exp_eq_exp_onSite` | `onSite x (exp A) = exp (onSite x A)` — bridge between single-site and many-body matrix exponential. Local Frobenius normed structure + `LinearMap.continuous_of_finiteDimensional` + `NormedSpace.map_exp` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}_eq_exp` | Tasaki eq. (2.2.11): `Û^(α)_θ_tot = exp(-iθ Ŝ_tot^(α))`. Composes `spinHalfRot{α}_eq_exp` (single site), `onSite_exp_eq_exp_onSite` (per-site bridge), and `Matrix.exp_sum_of_commute` (commuting-summand exp = noncommProd of exps) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}_commute_of_commute` | Tasaki §2.2 (2.2.12) → (2.2.13): `Commute A (Ŝ_tot^(α)) → Commute A (Û^(α)_θ_tot)`. Generic operator version, follows from `Commute.exp_right` after rewriting `Û` via `_eq_exp` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{Plus,Minus}_exp_commute_of_commute` | ladder version: `Commute A (Ŝ^±_tot) → Commute A (exp(c • Ŝ^±_tot))` for any `c : ℂ` (useful for U(1) symmetry) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}_conjTranspose_mul_self` | `(Û^(α)_θ_tot)ᴴ * Û^(α)_θ_tot = 1` (unitarity). Derived from `exp_mem_unitary_of_mem_skewAdjoint` after recognizing `-iθ Ŝ_tot^(α)` as skew-adjoint | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}_conj_eq_self_of_commute` | Tasaki eq. (2.2.13) finite form: `Commute A (Ŝ_tot^(α)) → (Û^(α)_θ_tot)ᴴ * A * Û^(α)_θ_tot = A`. Combines `_commute_of_commute` with unitarity | `Quantum/TotalSpin.lean` |
| `IsInMagnetizationSubspace` | predicate for the magnetization-`M` eigenspace `H_M` (Tasaki eq. (2.2.9)/(2.2.10)) | `Quantum/MagnetizationSubspace.lean` |
| `magnetizationSubspace M` | the magnetization-`M` eigenspace as a `Submodule ℂ ((Λ → Fin 2) → ℂ)` | `Quantum/MagnetizationSubspace.lean` |
| `basisVec_mem_magnetizationSubspace` | `|σ⟩ ∈ H_{|σ|/2}` — basis states lie in their magnetization subspace | `Quantum/MagnetizationSubspace.lean` |
| `magnetizationSubspace_disjoint` | distinct sectors `H_M ⊓ H_{M'} = ⊥` (`M ≠ M'`) — eigenvalue uniqueness | `Quantum/MagnetizationSubspace.lean` |
| `iSup_magnetizationSubspace_eq_top` | `⨆_M H_M = ⊤` — every vector decomposes as a sum across sectors | `Quantum/MagnetizationSubspace.lean` |
| `magnetizationSubspace_eq_eigenspace` | bridge `H_M = (Ŝ_tot^(3) as End).eigenspace M` (used to inherit `iSupIndep`) | `Quantum/MagnetizationSubspace.lean` |
| `magnetizationSubspace_iSupIndep` | `iSupIndep`: each sector is disjoint from the supremum of all others | `Quantum/MagnetizationSubspace.lean` |
| `magnetizationSubspace_isInternal` | `DirectSum.IsInternal`: full direct-sum decomposition `H = ⊕_M H_M` (Tasaki eqs. (2.2.9)/(2.2.10)) | `Quantum/MagnetizationSubspace.lean` |

### Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 eq. (2.2.16), p. 24.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfDot x y` | `Ŝ_x · Ŝ_y := Σ_{α} onSite x Ŝ^(α) · onSite y Ŝ^(α)` | `Quantum/SpinDot.lean` |
| `spinHalfDot_eq_plus_minus` | `Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^(3) Ŝ_y^(3)` (Tasaki (2.2.16)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_comm` | `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x` | `Quantum/SpinDot.lean` |
| `spinHalfDot_self` | `Ŝ_x · Ŝ_x = (3/4) · 1` (the S(S+1) = 3/4 identity for S = 1/2) | `Quantum/SpinDot.lean` |
| `spinHalfDot_isHermitian` | `Ŝ_x · Ŝ_y` is Hermitian | `Quantum/SpinDot.lean` |
| `totalSpinHalfSquared_eq_sum_dot` | `(Ŝ_tot)² = Σ_{x,y} Ŝ_x · Ŝ_y` | `Quantum/SpinDot.lean` |
| `spinHalfPairSpinSq` / `spinHalfPairSpinSq_eq` | `(Ŝ_x + Ŝ_y)² = 2·(Ŝ_x · Ŝ_y) + Ŝ_x · Ŝ_x + Ŝ_y · Ŝ_y` (Tasaki (2.2.18)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_commutator_totalSpinHalfOp{1,2,3}` | `[Ŝ_x · Ŝ_y, Ŝ_tot^(α)] = 0` for α ∈ {1, 2, 3} (SU(2) invariance, Tasaki (2.2.17)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_commutator_totalSpinHalfOpPlus/Minus` | `[Ŝ_x · Ŝ_y, Ŝ^±_tot] = 0` (ladder-operator version of SU(2) invariance) | `Quantum/SpinDot.lean` |
| `spinHalfDot_mulVec_basisVec_parallel` | `Ŝ_x · Ŝ_y |σ⟩ = (1/4) |σ⟩` when `σ x = σ y` and `x ≠ y` (Tasaki (2.2.19) parallel case) | `Quantum/SpinDot.lean` |
| `spinHalfDot_mulVec_basisVec_both_up/down` | `Ŝ_x · Ŝ_y |↑↑⟩ = (1/4) |↑↑⟩`, `Ŝ_x · Ŝ_y |↓↓⟩ = (1/4) |↓↓⟩` (Tasaki (2.2.19) triplet `m = ±1`) | `Quantum/SpinDot.lean` |
| `basisSwap` / `basisSwap_involutive` / `basisSwap_antiparallel` | site-swap of `σ` at `x, y`, involutive and preserves anti-parallelism | `Quantum/SpinDot.lean` |
| `spinHalfDot_mulVec_basisVec_antiparallel` | `Ŝ_x · Ŝ_y |σ⟩ = (1/2) |swap σ⟩ - (1/4) |σ⟩` when `σ x ≠ σ y` (anti-parallel case) | `Quantum/SpinDot.lean` |
| `spinHalfDot_mulVec_singlet` | singlet eigenvalue `Ŝ_x · Ŝ_y (|σ⟩ - |swap σ⟩) = -(3/4) (|σ⟩ - |swap σ⟩)` (Tasaki (2.2.19) singlet `S = 0`) | `Quantum/SpinDot.lean` |
| `spinHalfDot_mulVec_triplet_anti` | triplet `m = 0` eigenvalue `Ŝ_x · Ŝ_y (|σ⟩ + |swap σ⟩) = (1/4) (|σ⟩ + |swap σ⟩)` (Tasaki (2.2.19) triplet `m = 0`) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian` | `H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` (general Heisenberg-type Hamiltonian) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_commutator_totalSpinHalfOp{1,2,3}` | `[H, Ŝ_tot^(α)] = 0` for all axes (Tasaki (2.2.13) SU(2) invariance) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_commutator_totalSpinHalfOp{Plus,Minus}` | `[H, Ŝ^±_tot] = 0` (ladder form of SU(2) invariance) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_commute_totalSpinHalfSquared` | `Commute H Ŝtot²` — the Casimir operator-level form of SU(2) invariance (consequence of `[H, Ŝtot^α] = 0` for each α, via `Commute.mul_right` and `.add_right`) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_preserves_totalSpinHalfSquared_eigenvalue` | if `Ŝtot² · v = S · v` then `Ŝtot² · (H · v) = S · (H · v)` — operator-level simultaneous diagonalisation of `H` and the SU(2) Casimir | `Quantum/SpinDot.lean` |
| `spinHalfOpPlus_mul_pauliZ` / `pauliZ_mul_spinHalfOpPlus` | `σ^+ · σ^z = -σ^+` and `σ^z · σ^+ = σ^+` — the (anti)commutation at the single-site Pauli algebra level, used for the Jordan-Wigner cross-site CAR | `Quantum/SpinHalfBasis.lean` |
| `totalSpinHalfSquared_mulVec_basisVec_const` | `Ŝ_tot² |s s … s⟩ = (N(N+2)/4) |s s … s⟩` for any constant `s : Fin 2` (Casimir eigenvalue at maximum total spin `S = N/2`) | `Quantum/SpinDot.lean` |
| `totalSpinHalfSquared_mulVec_basisVec_all_up/down` | specializations of the above to `s = 0` (all-up) and `s = 1` (all-down) | `Quantum/SpinDot.lean` |
| `totalSpinHalfSquared_mulVec_totalSpinHalfOp{Minus,Plus}_pow_basisVec_const` | for any `s : Fin 2` and `k : ℕ`, `Ŝtot² · (Ŝtot^∓)^k · |s…s⟩ = (|Λ|·(|Λ|+2)/4) · (Ŝtot^∓)^k · |s…s⟩` — the iterated ladder iterates remain in the maximum-total-spin SU(2) representation `S = Smax = |Λ|/2` (Casimir invariance, Tasaki §2.4) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_basisVec_const` | `H |s…s⟩ = (Σ_{x,y} J(x,y)·(if x=y then 3/4 else 1/4)) · |s…s⟩` — every Heisenberg-type Hamiltonian acts on a uniformly-aligned basis state as a scalar; bilinear-sum lift of Tasaki §2.4 eq. (2.4.5), p. 32 (`-Ŝ_x·Ŝ_y |Φ↑⟩ = -S² |Φ↑⟩` for `S = 1/2`, `x ≠ y`), with the diagonal `S(S+1) = 3/4` contribution recorded explicitly | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_basisVec_all_up/down` | specialisations of the above to `s = 0` (all-up) / `s = 1` (all-down) — the eigenvector property of the fully-polarised states; ground-state status (Tasaki's `E_GS = -|B|·S²`) requires extra ferromagnetic structure on `J` and is not asserted here | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_basisVec_const` | `H · (Ŝ_tot^+ · |s…s⟩) = c_J · (Ŝ_tot^+ · |s…s⟩)` — `Ŝ_tot^+` preserves the H-eigenvalue on a constant-spin basis state (corollary of SU(2) invariance, Tasaki §2.4 (2.4.7), p. 33) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_basisVec_const` | same with `Ŝ_tot^-` — the canonical lowering ladder Tasaki uses to enumerate the ferromagnetic ground states `|Φ_M⟩` (eq. (2.4.9), p. 33) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_const` | iterated form: for any constant `s : Fin 2` and any `k : ℕ`, `H · ((Ŝ_tot^-)^k · |s…s⟩) = c_J · ((Ŝ_tot^-)^k · |s…s⟩)`; specialised at `s = 0` this gives the unnormalised Tasaki §2.4 (2.4.9), p. 33 — every iterate `(Ŝ_tot^-)^k · |Φ↑⟩` lies in the same H-eigenspace as `|Φ↑⟩` | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_const` | companion iterated form for `Ŝ_tot^+`: for any constant `s : Fin 2` and any `k : ℕ`, `H · ((Ŝ_tot^+)^k · |s…s⟩) = c_J · ((Ŝ_tot^+)^k · |s…s⟩)` (corollary of SU(2) invariance, Tasaki §2.4 (2.4.7), iterated) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_commute_totalSpinHalfRot{1,2,3}` | for any `J` and `θ : ℝ`, `H` commutes with the global rotation `Û^(α)_θ = exp(-iθ Ŝ_tot^α)` (composes `heisenbergHamiltonian_commutator_totalSpinHalfOp{α}` with `totalSpinHalfRot{α}_commute_of_commute`; the operator-level form of Tasaki §2.4 (2.4.7), p. 33) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfRot{1,2,3}_basisVec_const` | for any `J`, `θ`, and constant `s : Fin 2`, `H · (Û^(α)_θ · |s…s⟩) = c_J · (Û^(α)_θ · |s…s⟩)` — the rotated (single-axis) constant-spin state shares the H-eigenvalue (Tasaki §2.4 (2.4.7), p. 33) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfRot32_basisVec_const` | for any `J`, `θ`, `ϕ`, and constant `s : Fin 2`, `H · (Û^(3)_ϕ · Û^(2)_θ · |s…s⟩) = c_J · (Û^(3)_ϕ · Û^(2)_θ · |s…s⟩)` — the two-step spin-coherent state of Tasaki eq. (2.4.6) (`|Ξ_θ,ϕ⟩` for `s = 0`) is an H-eigenvector with the same eigenvalue as the constant configuration (Tasaki eq. (2.4.7), p. 33) | `Quantum/SpinDot.lean` |
| `totalSpinHalfSquared_mulVec_two_site_singlet` | `Ŝ_tot² (|↑↓⟩ - |↓↑⟩) = 0` for `Λ = Fin 2` (singlet, `S = 0`) | `Quantum/SpinDot.lean` |
| `totalSpinHalfSquared_mulVec_two_site_triplet_zero` | `Ŝ_tot² (|↑↓⟩ + |↓↑⟩) = 2(|↑↓⟩ + |↓↑⟩)` for `Λ = Fin 2` (triplet `m = 0`, `S = 1`) | `Quantum/SpinDot.lean` |
| `totalSpinHalfOp3_mulVec_two_site_singlet` | the two-site singlet has zero `Ŝ_tot^(3)` magnetization | `Quantum/SpinDot.lean` |
| `onSite_commutator_totalOnSite` | `[onSite x Sα, Σ_z onSite z Sβ] = onSite x [Sα, Sβ]` | `Quantum/TotalSpin.lean` |

### One-dimensional open-chain quantum Ising

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.3 eq. (3.3.1), p. 55 (transverse-field Ising on an open
chain). Our formalization uses the Pauli convention `σ = 2·S` and an
explicit bond coupling `J`.

| Lean name | Statement | File |
|---|---|---|
| `quantumIsingHamiltonian N J h` | `H = -J Σ σ^z_i σ^z_{i+1} - h Σ σ^x_i` | `Quantum/IsingChain.lean` |
| `quantumIsingHamiltonian_isHermitian` | `H` is Hermitian for real `J`, `h` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState β J h N` | `gibbsState β (quantumIsingHamiltonian N J h)` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState_isHermitian` | the Ising-chain Gibbs state `ρ_β` is Hermitian | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState_commute_hamiltonian` | `[ρ_β, H_Ising] = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_zero` | infinite-temperature closed form `⟨A⟩_0 = (1/dim) · Tr A` (independent of `J, h`) | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_im_of_isHermitian` | for Hermitian `O`, `(⟨O⟩_β).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_commutator_hamiltonian` | conservation `⟨[H_Ising, A]⟩_β = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_hamiltonian_im` | `(⟨H_Ising⟩_β).im = 0` (energy expectation is real) | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_mul_hamiltonian_im` | for Hermitian `O`, `(⟨H_Ising · O⟩_β).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_hamiltonian_sq_im` | `(⟨H_Ising^2⟩_β).im = 0` (energy-squared expectation real) | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_hamiltonian_pow_im` | `(⟨H_Ising^n⟩_β).im = 0` for any `n : ℕ` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_anticommutator_im` | for Hermitian `A, B`, `(⟨A·B + B·A⟩_β).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_commutator_re` | for Hermitian `A, B`, `(⟨A·B − B·A⟩_β).re = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsHamiltonianVariance_im` | `(Var_β(H_Ising)).im = 0` (energy variance real) | `Quantum/IsingChain.lean` |
| `quantumIsing_partitionFn_im` | `(partitionFn β H_Ising).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_ofReal_re_eq` | for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for the Ising Hamiltonian | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_self_eq` | `⟨H_Ising⟩_β = -J · ∑ ⟨σ^z σ^z⟩_β + (-h) · ∑ ⟨σ^x⟩_β` (energy as bond + transverse-field decomposition) | `Quantum/IsingChain.lean` |

### Gibbs state (Tasaki §3.3)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.3.

All theorems in this module are fully proved with **zero `sorry`**.

| Lean name | Statement | File |
|---|---|---|
| `gibbsExp β H` | `exp(-βH) := Matrix.exp (-β • H)` | `Quantum/GibbsState.lean` |
| `gibbsExp_isHermitian` | `exp(-βH)` is Hermitian (when `H` is Hermitian) | `Quantum/GibbsState.lean` |
| `gibbsExp_zero` | `exp(-0·H) = 1` (Tasaki §3.3, pp. 75–78) | `Quantum/GibbsState.lean` |
| `gibbsExp_add` | `exp(-(β₁+β₂)H) = exp(-β₁H) · exp(-β₂H)` (one-parameter group) | `Quantum/GibbsState.lean` |
| `gibbsExp_add_of_commute_hamiltonians` | `exp(-β(H₁+H₂)) = exp(-βH₁) · exp(-βH₂)` for commuting `H₁, H₂` | `Quantum/GibbsState.lean` |
| `gibbsExp_neg_mul_self` | `exp(βH) · exp(-βH) = 1` | `Quantum/GibbsState.lean` |
| `gibbsExp_self_mul_neg` | `exp(-βH) · exp(βH) = 1` | `Quantum/GibbsState.lean` |
| `gibbsExp_isUnit` | `exp(-βH)` is invertible | `Quantum/GibbsState.lean` |
| `gibbsExp_ne_zero` | `exp(-βH) ≠ 0` (corollary of `gibbsExp_isUnit`) | `Quantum/GibbsState.lean` |
| `gibbsState_ne_zero` | `ρ_β ≠ 0` when `Z(β) ≠ 0` | `Quantum/GibbsState.lean` |
| `gibbsState_inv` | `(ρ_β)⁻¹ = Z(β) · e^{βH}` when `Z(β) ≠ 0` (general matrix inverse, generalises `gibbsState_zero_inv`) | `Quantum/GibbsState.lean` |
| `partitionFn_smul_gibbsState_eq_gibbsExp` | `Z(β) · ρ_β = e^{-βH}` when `Z(β) ≠ 0` (canonical rescaled identity) | `Quantum/GibbsState.lean` |
| `partitionFn_mul_gibbsExpectation_eq` | `Z(β) · ⟨A⟩_β = Tr(e^{-βH} · A)` when `Z(β) ≠ 0` (canonical unnormalised expectation) | `Quantum/GibbsState.lean` |
| `gibbsExp_natCast_mul` | `exp(-(n·β)H) = (exp(-βH))^n` for `n : ℕ` (exact discrete semigroup identity) | `Quantum/GibbsState.lean` |
| `gibbsExp_two_mul` | `exp(-(2β)H) = exp(-βH) · exp(-βH)` | `Quantum/GibbsState.lean` |
| `gibbsExp_inv` | `(exp(-βH))⁻¹ = exp(βH)` (matrix inverse made explicit) | `Quantum/GibbsState.lean` |
| `gibbsExp_intCast_mul` | `exp(-(n·β)H) = (exp(-βH))^n` for `n : ℤ` (integer-power extension) | `Quantum/GibbsState.lean` |
| `partitionFn β H` | `Z := Matrix.trace (exp(-βH))` | `Quantum/GibbsState.lean` |
| `partitionFn_zero` | `Z(0) = Fintype.card (Λ → Fin 2)` (dimension of the Hilbert space) | `Quantum/GibbsState.lean` |
| `partitionFn_zero_ne_zero` | `Z(0) ≠ 0` (concrete sorry-free proof that the partition function is nonzero at β = 0) | `Quantum/GibbsState.lean` |
| `Matrix.IsHermitian.trace_im` | for any Hermitian `A : Matrix n n ℂ`, `A.trace.im = 0` (generic helper) | `Quantum/GibbsState.lean` |
| `partitionFn_im_of_isHermitian` | for Hermitian `H`, `(partitionFn β H).im = 0` (Z is real) | `Quantum/GibbsState.lean` |
| `gibbsState_mul_self_trace` | `Tr(ρ_β²) = Z(2β) / Z(β)²` (purity / Rényi-2 entropy precursor) | `Quantum/GibbsState.lean` |
| `gibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for any `n : ℕ` (Rényi-n entropy precursor) | `Quantum/GibbsState.lean` |
| `gibbsState_zero` | `ρ_0 = (1/dim) · I` (maximally mixed state at infinite temperature) | `Quantum/GibbsState.lean` |
| `gibbsState_zero_inv` | `ρ_0⁻¹ = dim · I` (matrix inverse at β = 0) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_zero` | `⟨A⟩_0 = (1/dim) · Tr A` (high-temperature limit) | `Quantum/GibbsState.lean` |
| `gibbsState β H` | `ρ := (1/Z) • exp(-βH)` | `Quantum/GibbsState.lean` |
| `gibbsState_trace` | `Tr(ρ) = 1` | `Quantum/GibbsState.lean` |
| `gibbsState_isHermitian` | `ρ` is Hermitian | `Quantum/GibbsState.lean` |
| `gibbsExpectation β H O` | `⟨O⟩ := Matrix.trace (ρ * O)` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_one` | `⟨1⟩ = 1` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_add` | `⟨O₁ + O₂⟩ = ⟨O₁⟩ + ⟨O₂⟩` (linearity in observable) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_smul` | `⟨c · O⟩ = c · ⟨O⟩` (scalar linearity, `c : ℂ`) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_neg` | `⟨-O⟩ = -⟨O⟩` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_sub` | `⟨A - B⟩ = ⟨A⟩ - ⟨B⟩` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_sum` | `⟨∑ i ∈ s, f i⟩ = ∑ i ∈ s, ⟨f i⟩` (finite-sum linearity) | `Quantum/GibbsState.lean` |
| `gibbsExp_commute_hamiltonian` | `[exp(-βH), H] = 0` (Tasaki §3.3, p. 80) | `Quantum/GibbsState.lean` |
| `gibbsState_commute_hamiltonian` | `[ρ_β, H] = 0`, i.e. `ρ_β` is stationary under the dynamics generated by `H` (Tasaki §3.3, p. 80) | `Quantum/GibbsState.lean` |
| `Matrix.trace_mul_star_of_isHermitian` | `star (Tr(A · B)) = Tr(A · B)` for Hermitian `A, B : Matrix n n ℂ` (algebraic core, Gibbs-independent) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_star_of_isHermitian` | `star ⟨O⟩_β = ⟨O⟩_β` for Hermitian `H`, `O` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_im_of_isHermitian` | `(⟨O⟩_β).im = 0` for Hermitian `H`, `O` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_ofReal_re_eq_of_isHermitian` | `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` for Hermitian `H`, `O` (real-cast equality) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_mul_hamiltonian_comm` | `⟨H · A⟩_β = ⟨A · H⟩_β` for any `A` (Tasaki §3.3, p. 80) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_mul_comm_of_commute_hamiltonian` | for any conserved `A` (`[A, H] = 0`), `⟨A · O⟩_β = ⟨O · A⟩_β` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_commutator_eq_zero_of_commute_hamiltonian` | for any conserved `A`, `⟨A · O − O · A⟩_β = 0` (selection rule) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_commutator_hamiltonian` | `⟨[H, A]⟩_β = 0` (conservation law) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_hamiltonian_im` | `(⟨H⟩_β).im = 0` for Hermitian `H` (real energy expectation) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_sq_im_of_isHermitian` | `(⟨O · O⟩_β).im = 0` for Hermitian `H, O` (second-moment realness, variance precursor) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_pow_im_of_isHermitian` | `(⟨O^n⟩_β).im = 0` for Hermitian `H, O`, any `n : ℕ` (all natural-power moments real) | `Quantum/GibbsState.lean` |
| `gibbsVariance β H O` | `Var_β(O) := ⟨O · O⟩_β − ⟨O⟩_β²` (canonical-ensemble variance) | `Quantum/GibbsState.lean` |
| `gibbsVariance_eq` | unfolding lemma for `gibbsVariance` | `Quantum/GibbsState.lean` |
| `gibbsVariance_im_of_isHermitian` | `(Var_β(O)).im = 0` for Hermitian `H, O` (variance is real) | `Quantum/GibbsState.lean` |
| `gibbsVariance_zero` | at β = 0, `Var_0(O) = (1/dim) · Tr(O²) − ((1/dim) · Tr O)²` | `Quantum/GibbsState.lean` |
| `gibbsVariance_eq_centered_sq` | `Var_β(O) = ⟨(O − ⟨O⟩_β · 1) · (O − ⟨O⟩_β · 1)⟩_β` (centered-square form, `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsCovariance β H A B` | `Cov_β(A, B) := ⟨A · B⟩_β − ⟨A⟩_β · ⟨B⟩_β` (canonical-ensemble complex covariance) | `Quantum/GibbsState.lean` |
| `gibbsCovariance_eq` | unfolding lemma for `gibbsCovariance` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_self_eq_variance` | `Cov_β(O, O) = Var_β(O)` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_sub_swap_eq_commutator` | `Cov_β(A, B) − Cov_β(B, A) = ⟨A · B − B · A⟩_β` (antisymmetric part = commutator expectation) | `Quantum/GibbsState.lean` |
| `gibbsCovariance_add_left` | `Cov_β(A₁ + A₂, B) = Cov_β(A₁, B) + Cov_β(A₂, B)` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_add_right` | `Cov_β(A, B₁ + B₂) = Cov_β(A, B₁) + Cov_β(A, B₂)` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_smul_left` | `Cov_β(c • A, B) = c · Cov_β(A, B)` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_smul_right` | `Cov_β(A, c • B) = c · Cov_β(A, B)` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_const_smul_one_left/right_eq_zero` | `Cov_β(c • 1, B) = 0` and `Cov_β(A, c • 1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_const_smul_one_left/right_eq_zero` | `Cov^s_β(c • 1, B) = 0` and `Cov^s_β(A, c • 1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm β H A B` | `Cov^s_β(A, B) := (1/2) · ⟨A · B + B · A⟩_β − ⟨A⟩_β · ⟨B⟩_β` (symmetric / real-valued covariance) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_self_eq_variance` | `Cov^s_β(O, O) = Var_β(O)` | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_im_of_isHermitian` | `(Cov^s_β(A, B)).im = 0` for Hermitian `H, A, B` | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_comm` | `Cov^s_β(A, B) = Cov^s_β(B, A)` (symmetric in observables) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_add_left/right` | additivity of `Cov^s_β` in each argument | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_smul_left/right` | scalar pull-out from each argument of `Cov^s_β` | `Quantum/GibbsState.lean` |
| `gibbsVariance_add` | `Var_β(A + B) = Var_β(A) + Var_β(B) + 2 · Cov^s_β(A, B)` (sum-of-observables variance identity) | `Quantum/GibbsState.lean` |
| `gibbsVariance_one` | `Var_β(1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsVariance_smul` | `Var_β(c • A) = c² · Var_β(A)` | `Quantum/GibbsState.lean` |
| `gibbsVariance_smul_one` | `Var_β(c • 1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsVariance_neg` | `Var_β(−A) = Var_β(A)` | `Quantum/GibbsState.lean` |
| `gibbsVariance_add_const_smul_one` | `Var_β(A + c • 1) = Var_β(A)` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsCovariance_eq_symm_add_half_commutator` | `Cov_β(A, B) = Cov^s_β(A, B) + (1/2) · ⟨A · B − B · A⟩_β` (symmetric / antisymmetric decomposition) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_eq_half_add_swap` | `Cov^s_β(A, B) = (1/2) · (Cov_β(A, B) + Cov_β(B, A))` | `Quantum/GibbsState.lean` |
| `gibbsCovariance_eq_symm_of_commute` | for commuting `A, B`, `Cov_β(A, B) = Cov^s_β(A, B)` | `Quantum/GibbsState.lean` |
| `Matrix.trace_mul_conjTranspose_swap_of_isHermitian` | `star Tr(ρ · X) = Tr(ρ · Xᴴ)` for Hermitian `ρ` (generic helper) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_star_swap_of_isHermitian` | `star ⟨A · B⟩_β = ⟨B · A⟩_β` for Hermitian `H, A, B` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_anticommutator_im` | `(⟨A·B + B·A⟩_β).im = 0` (anticommutator is real) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_commutator_re` | `(⟨A·B − B·A⟩_β).re = 0` (commutator is purely imaginary) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_mul_hamiltonian_im` | `(⟨H · O⟩_β).im = 0` for Hermitian `H, O` | `Quantum/GibbsState.lean` |

### Heisenberg chain (Tasaki §3.5)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.5, p. 89.

| Lean name | Statement | File |
|---|---|---|
| `LatticeSystem.Lattice.couplingOf G J` | the canonical pairwise coupling `Λ → Λ → ℂ` of a `SimpleGraph G` with uniform edge weight `J`: returns `J` on edges of `G`, zero otherwise (graph-centric bridge) | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.couplingOf_symm` / `_self` / `_real` | symmetry (from `G.Adj` symmetry), vanishing on the diagonal (from irreflexivity), and reality (for real edge weight) | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.pathGraph_adj_iff` / `cycleGraph_adj_iff` | path / cycle graph adjacency in the explicit `x.val + 1 = y.val ∨ ...` form used elsewhere in the codebase | `Lattice/Graph.lean` |
| `openChainCoupling N J` | coupling `Fin (N+1) → Fin (N+1) → ℂ`: returns `-J` on nearest-neighbour bonds, zero otherwise | `Quantum/HeisenbergChain.lean` |
| `periodicChainCoupling N J` | coupling `Fin (N+2) → Fin (N+2) → ℂ`: returns `-J` on nearest-neighbour bonds (mod N+2), zero otherwise | `Quantum/HeisenbergChain.lean` |
| `openChainCoupling_eq_couplingOf` | the open-chain coupling is `couplingOf (pathGraph (N+1)) (-J)` | `Quantum/HeisenbergChain.lean` |
| `periodicChainCoupling_eq_couplingOf` | the periodic-chain coupling is `couplingOf (cycleGraph (N+2)) (-J)` | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_isHermitian_of_real_symm` | for any real symmetric coupling `J` the Heisenberg Hamiltonian `H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` is Hermitian | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_couplingOf_isHermitian` | **graph-centric** Hermiticity: for any `SimpleGraph G` and real edge weight `J : ℂ`, the Heisenberg Hamiltonian `heisenbergHamiltonian (couplingOf G J)` is Hermitian. The chain instances are corollaries via the bridge theorems | `Quantum/HeisenbergChain.lean` |
| `LatticeSystem.Lattice.boxProd_decidableAdj` | `DecidableRel (G □ H).Adj` for the box product (mathlib provides only the bare definition); enables 2D / nD lattices via `couplingOf` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerChainGraph` | the **infinite** one-dimensional chain `ℤ` as a `SimpleGraph` (= `hasse ℤ`), the infinite-volume analogue of `pathGraph (N+1)` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerChainGraph_adj_iff` | adjacency: `a ~ b ↔ b = a + 1 ∨ a = b + 1` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerSquareLatticeGraph` | the **infinite** 2D square lattice on `ℤ × ℤ` as `integerChainGraph □ integerChainGraph`; infinite analogue of `squareLatticeCoupling` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerSquareLatticeGraph_adj_iff` | adjacency: nearest neighbour in one coordinate, equal in the other | `Lattice/Graph.lean` |
| `squareLatticeCoupling N J`, `squareLatticeHeisenberg_isHermitian` | the 2D open-boundary square lattice on `Fin (N+1) × Fin (N+1)` realised as `couplingOf (pathGraph (N+1) □ pathGraph (N+1)) (-J)`; Hermiticity is a one-line corollary of the graph-generic theorem above | `Quantum/HeisenbergChain.lean` |
| `squareTorusCoupling N J`, `squareTorusHeisenberg_isHermitian` | the 2D periodic square lattice (discrete torus) on `Fin (N+2) × Fin (N+2)` realised as `couplingOf (cycleGraph (N+2) □ cycleGraph (N+2)) (-J)`; Hermiticity is a one-line corollary | `Quantum/HeisenbergChain.lean` |
| `cubicLatticeCoupling N J`, `cubicLatticeHeisenberg_isHermitian` | the 3D open-boundary cubic lattice on `Fin (N+1)^3` realised as `couplingOf (pathGraph (N+1) □ pathGraph (N+1) □ pathGraph (N+1)) (-J)`; Hermiticity is a one-line corollary | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp{1,2,3}` | for any `SimpleGraph G` and edge weight `J : ℂ`, the Heisenberg Hamiltonian on `G` commutes with each total-spin component (free corollary of the generic-J theorems) | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_couplingOf_commute_totalSpinHalfSquared` | the same Hamiltonian commutes with the total-spin Casimir `Ŝ_tot²` (graph-centric SU(2) invariance) | `Quantum/HeisenbergChain.lean` |
| `heisenbergGibbsStateOnGraph β G J` | Gibbs state `gibbsState β (H_G_J)` for any finite graph `G` and complex edge weight `J` | `Quantum/HeisenbergChain.lean` |
| `heisenbergGibbsStateOnGraph_isHermitian` | Hermiticity when `J` is real | `Quantum/HeisenbergChain.lean` |
| `heisenbergGibbsStateOnGraph_commute_hamiltonian` | `Commute ρ_β H_G_J` (generic for any Gibbs state / Hamiltonian pair) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenberg_isHermitian` | specialization: the open-chain Heisenberg Hamiltonian is Hermitian | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenberg_isHermitian` | specialization: the periodic-chain Heisenberg Hamiltonian is Hermitian | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_gibbsExpectation_eq` | generic bond-sum decomposition `⟨H⟩_β = ∑ x, ∑ y, J x y · ⟨Ŝ_x · Ŝ_y⟩_β` (any Gibbs Hamiltonian, any coupling `J`) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_self_eq` | open-chain energy expectation as a sum over open-boundary bonds | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_self_eq` | periodic-chain energy expectation as a sum over periodic-boundary bonds | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState β J N` | `gibbsState β (heisenbergHamiltonian (openChainCoupling N J))` (open-chain Gibbs state) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState_isHermitian` | the open-chain Heisenberg Gibbs state `ρ_β` is Hermitian | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState_commute_hamiltonian` | `[ρ_β, H_open] = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_zero` | high-temperature closed form `⟨A⟩_0 = (1/dim) · Tr A` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_im_of_isHermitian` | for Hermitian `O`, `(⟨O⟩_β).im = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_commutator_hamiltonian` | conservation `⟨[H_open, A]⟩_β = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_hamiltonian_im` | `(⟨H_open⟩_β).im = 0` (energy expectation is real) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_mul_hamiltonian_im` | for Hermitian `O`, `(⟨H_open · O⟩_β).im = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_hamiltonian_sq_im` | `(⟨H_open^2⟩_β).im = 0` (energy-squared expectation real) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_hamiltonian_pow_im` | `(⟨H_open^n⟩_β).im = 0` for any `n : ℕ` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_anticommutator_im` | for Hermitian `A, B`, `(⟨A·B + B·A⟩_β).im = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_commutator_re` | for Hermitian `A, B`, `(⟨A·B − B·A⟩_β).re = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsHamiltonianVariance_im` | `(Var_β(H_open)).im = 0` (energy variance real) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenberg_partitionFn_im` | `(partitionFn β H_open).im = 0` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_ofReal_re_eq` | for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for the open-chain Hamiltonian | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsState β J N` | analogous Gibbs state for the periodic-chain Hamiltonian | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsState_isHermitian` | periodic-chain Gibbs state Hermiticity | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsState_commute_hamiltonian` | `[ρ_β, H_periodic] = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_zero` | periodic-chain high-temperature closed form | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_im_of_isHermitian` | for Hermitian `O`, `(⟨O⟩_β).im = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_commutator_hamiltonian` | conservation `⟨[H_periodic, A]⟩_β = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_hamiltonian_im` | `(⟨H_periodic⟩_β).im = 0` (energy expectation is real) | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_mul_hamiltonian_im` | for Hermitian `O`, `(⟨H_periodic · O⟩_β).im = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_hamiltonian_sq_im` | `(⟨H_periodic^2⟩_β).im = 0` (energy-squared expectation real) | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_hamiltonian_pow_im` | `(⟨H_periodic^n⟩_β).im = 0` for any `n : ℕ` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_anticommutator_im` | for Hermitian `A, B`, `(⟨A·B + B·A⟩_β).im = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_commutator_re` | for Hermitian `A, B`, `(⟨A·B − B·A⟩_β).re = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsHamiltonianVariance_im` | `(Var_β(H_periodic)).im = 0` (energy variance real) | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenberg_partitionFn_im` | `(partitionFn β H_periodic).im = 0` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_ofReal_re_eq` | for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for the periodic-chain Hamiltonian | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_two_site_eq` | for `N = 1` (the 2-site open chain on `Fin 2`), `H_open = -2J · spinHalfDot 0 1` (explicit one-bond reduction; Tasaki §2.4 simplest concrete instance) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_all_up` | `H_open(N=1) · |↑↑⟩ = -(J/2) · |↑↑⟩` — `|↑↑⟩` lies in the `S = 1` triplet sector and is an exact eigenvector with eigenvalue `-J/2` (this is the ferromagnetic ground state for `J < 0`) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_singlet` | `H_open(N=1) · (|↑↓⟩ - |↓↑⟩) = (3J/2) · (|↑↓⟩ - |↓↑⟩)` — singlet eigenvalue, the antiferromagnetic ground state for `J > 0` (Tasaki §2.5 concrete instance) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_all_down` | `H_open(N=1) · |↓↓⟩ = -(J/2) · |↓↓⟩` — all-down state has the same eigenvalue as all-up (both are `S = 1` triplet states) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_triplet_zero` | `H_open(N=1) · (|↑↓⟩ + |↓↑⟩) = -(J/2) · (|↑↓⟩ + |↓↑⟩)` — triplet `m = 0` state, completing the 3-fold degenerate triplet representation `S = 1` with eigenvalue `-J/2` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_three_site_eq` | for `N = 2` (the 3-site open chain on `Fin 3`, 2 bonds), `H_open = -2J · (spinHalfDot 0 1 + spinHalfDot 1 2)` — explicit two-bond reduction | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_three_site_mulVec_basisVec_all_up` | `H_open(N=2) · |↑↑↑⟩ = -J · |↑↑↑⟩` — confirming the linear scaling `E(|↑..↑⟩) = -N·J/2` (here `N = 2` bonds, `J = 1` per bond) | `Quantum/HeisenbergChain.lean` |
| `openChainCoupling_sum_eq` | for any `N : ℕ`, `Σ_{x,y ∈ Fin (N+1)} openChainCoupling N J x y = -(2N · J : ℂ)` (the bond-counting lemma: each of the `N` unordered nearest-neighbour bonds is counted in both orientations) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_mulVec_basisVec_const` | for any `N : ℕ`, `J : ℝ`, and constant `s : Fin 2`, `H_open · |s..s⟩ = -(N·J/2 : ℂ) · |s..s⟩` — both `s = 0` (all-up) and `s = 1` (all-down) share the same eigenvalue by SU(2) symmetry | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_mulVec_basisVec_all_up` | `s = 0` specialisation of the above (Tasaki §2.4 (2.4.5)/(2.4.1) ferromagnetic ground-state energy `E_GS = -|B|·S²` for `S = 1/2`, `|B| = N` bonds) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_mulVec_basisVec_all_down` | `s = 1` specialisation: same eigenvalue `-(N·J/2)` for the all-down state by SU(2) symmetry | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up` | for any `N : ℕ`, `J : ℝ`, `k : ℕ`, `H_open · ((Ŝtot^-)^k · |↑..↑⟩) = -(N·J/2 : ℂ) · ((Ŝtot^-)^k · |↑..↑⟩)` — the unnormalised Tasaki §2.4 (2.4.9) ferromagnetic ground states `|Φ_M⟩` made explicit on the chain (combines PRs #82 + #98) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down` | dual ladder from `|↓..↓⟩`, same eigenvalue `-(N·J/2)` | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem` | `H_open` preserves every magnetisation subspace `H_M` (chain specialisation of PR #91) | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem` | `H_periodic` preserves every magnetisation subspace `H_M` (chain specialisation of PR #91) | `Quantum/HeisenbergChain.lean` |

### Single-mode fermion (P2 skeleton)

Phase 2 entry point: the canonical anticommutation algebra of a single
fermion mode acting on `ℂ²` with computational basis
`|0⟩` (vacuum) and `|1⟩` (occupied).

| Lean name | Statement | File |
|---|---|---|
| `fermionAnnihilation` | `c = !![0, 1; 0, 0] = |0⟩⟨1|` | `Fermion/Mode.lean` |
| `fermionCreation` | `c† = !![0, 0; 1, 0] = |1⟩⟨0|` | `Fermion/Mode.lean` |
| `fermionNumber` | `n = !![0, 0; 0, 1] = |1⟩⟨1|` | `Fermion/Mode.lean` |
| `fermionNumber_eq_creation_mul_annihilation` | `n = c† · c` | `Fermion/Mode.lean` |
| `fermionAnnihilation_sq` | `c² = 0` | `Fermion/Mode.lean` |
| `fermionCreation_sq` | `(c†)² = 0` | `Fermion/Mode.lean` |
| `fermionAnticomm_self` | `c · c† + c† · c = 1` (single-mode CAR) | `Fermion/Mode.lean` |
| `fermionNumber_sq` | `n² = n` (idempotent number operator) | `Fermion/Mode.lean` |
| `fermionAnnihilation_conjTranspose` | `cᴴ = c†` | `Fermion/Mode.lean` |
| `fermionCreation_conjTranspose` | `(c†)ᴴ = c` | `Fermion/Mode.lean` |
| `fermionNumber_isHermitian` | `n` is Hermitian | `Fermion/Mode.lean` |
| `fermionVacuum`, `fermionOccupied` | basis vectors `|0⟩ = (1, 0)`, `|1⟩ = (0, 1)` | `Fermion/Mode.lean` |
| `fermionAnnihilation_mulVec_vacuum` / `_occupied` | `c|0⟩ = 0`, `c|1⟩ = |0⟩` | `Fermion/Mode.lean` |
| `fermionCreation_mulVec_vacuum` / `_occupied` | `c†|0⟩ = |1⟩`, `c†|1⟩ = 0` | `Fermion/Mode.lean` |
| `fermionNumber_mulVec_vacuum` / `_occupied` | `n|0⟩ = 0`, `n|1⟩ = |1⟩` | `Fermion/Mode.lean` |
| `fermionAnnihilation_eq_spinHalfOpPlus` | `c = σ^+` (computational-basis identification) | `Fermion/Mode.lean` |
| `fermionCreation_eq_spinHalfOpMinus` | `c† = σ^-` | `Fermion/Mode.lean` |

### Multi-mode fermion via Jordan–Wigner (P2 backbone)

| Lean name | Statement | File |
|---|---|---|
| `jwString N i` | `∏_{j.val < i.val} σ^z_j` (noncomm-product, pairwise commutativity from `onSite_mul_onSite_of_ne`) | `Fermion/JordanWigner.lean` |
| `jwString_zero` | `jwString N 0 = 1` (empty product) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation N i` | `c_i = jwString_i · σ^+_i` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation N i` | `c_i† = jwString_i · σ^-_i` | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_zero` | `c_0 = σ^+_0` (no JW string at the leftmost site) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_zero` | `c_0† = σ^-_0` | `Fermion/JordanWigner.lean` |
| `jwString_commute_onSite` | `Commute (jwString N i) (onSite i A)` (string commutes past same-site operators) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_sq` | `c_i² = 0` (Pauli exclusion) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_sq` | `(c_i†)² = 0` | `Fermion/JordanWigner.lean` |
| `jwString_isHermitian` | `(jwString N i)ᴴ = jwString N i` (product of pairwise-commuting Hermitian σ^z is Hermitian) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_conjTranspose` | `(c_i)ᴴ = c_i†` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_conjTranspose` | `(c_i†)ᴴ = c_i` | `Fermion/JordanWigner.lean` |
| `jwString_sq` | `(jwString N i)² = 1` | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber N i` | `n_i := c_i† · c_i` (site-occupation number operator) | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_eq_onSite` | `n_i = onSite i (σ^- · σ^+)` (JW strings cancel via `J² = 1`) | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_isHermitian` | `n_i` is Hermitian | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_sq` | `n_i² = n_i` (idempotent, eigenvalues 0, 1) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnticomm_self` | `c_i · c_i† + c_i† · c_i = 1` (same-site CAR) | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_commute` | `Commute (n_i) (n_j)` for any sites (simultaneously diagonal) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber N` | `N̂ := Σ_i n_i` (total particle-number operator) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_isHermitian` | `N̂` is Hermitian | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_anticomm_two_site_cross` | simplest nontrivial cross-site CAR on `Fin 2`: `c_0 · c_1 + c_1 · c_0 = 0` (JW string at site 1 is `σ^z_0`, combined with `σ^+ σ^z = -σ^+` and `σ^z σ^+ = σ^+`) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_anticomm_two_site_cross` | adjoint form: `c_0† · c_1† + c_1† · c_0† = 0` on `Fin 2`, obtained by taking `conjTranspose` of the annihilation version | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_creation_anticomm_two_site_cross` | mixed cross-site: `c_0 · c_1† + c_1† · c_0 = 0` on `Fin 2` (same proof template as the annihilation-only version with `σ^+_1` replaced by `σ^-_1` at site 1) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_annihilation_anticomm_two_site_cross` | fourth off-diagonal CAR: `c_0† · c_1 + c_1 · c_0† = 0` on `Fin 2` (adjoint of the previous; completes the 2-site off-diagonal CAR relations) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_anticomm_zero_one` | generalisation to any chain length: `c_0 · c_1 + c_1 · c_0 = 0` on `Fin (N+1)` for any `N ≥ 1` (the JW string at site 1 is uniformly `σ^z_0` independent of `N`) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_anticomm_zero_one` | dual: `c_0† · c_1† + c_1† · c_0† = 0` on `Fin (N+1)`, `N ≥ 1` (adjoint of the above) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_one` | mixed: `c_0 · c_1† + c_1† · c_0 = 0` on `Fin (N+1)`, `N ≥ 1` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_one` | mixed dual: `c_0† · c_1 + c_1 · c_0† = 0` on `Fin (N+1)`, `N ≥ 1` | `Fermion/JordanWigner.lean` |
| `jwString_succ_eq` | recursive factorisation of the JW string: `jwString N ⟨i+1, _⟩ = jwString N i * onSite i pauliZ` (key general lemma for proving jwString at any specific site without raw `Finset.noncommProd` manipulation) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_anticomm_zero_two_fin_three` | first 3-site cross-site CAR: `c_0 · c_2 + c_2 · c_0 = 0` on `Fin 3` (using `jwString_succ_eq` to factor `jwString 2 2 = σ^z_0 · σ^z_1`) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_anticomm_zero_two_fin_three` | dual: `c_0† · c_2† + c_2† · c_0† = 0` on `Fin 3` (adjoint of the previous) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_two_fin_three` | mixed: `c_0 · c_2† + c_2† · c_0 = 0` on `Fin 3` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_two_fin_three` | mixed dual: `c_0† · c_2 + c_2 · c_0† = 0` on `Fin 3` (adjoint of the previous) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_anticomm_zero_two_general` | generalised to any N ≥ 2: `c_0 · c_2 + c_2 · c_0 = 0` on `Fin (N+1)` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_anticomm_zero_two_general` | dual: `c_0† · c_2† + c_2† · c_0† = 0` for any N ≥ 2 (adjoint) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_two_general` | mixed: `c_0 · c_2† + c_2† · c_0 = 0` for any N ≥ 2 | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_two_general` | mixed dual: `c_0† · c_2 + c_2 · c_0† = 0` for any N ≥ 2 (adjoint) | `Fermion/JordanWigner.lean` |
| `spinHalfOpPlus_mul_self` / `spinHalfOpPlus_mul_spinHalfOpMinus_mul_spinHalfOpPlus` | Pauli helper identities `σ^+ σ^+ = 0` and `σ^+ σ^- σ^+ = σ^+` | `Quantum/SpinHalfBasis.lean` |
| `fermionMultiNumber_commutator_fermionMultiAnnihilation_self` | `[n_i, c_i] = -c_i` (number / annihilation commutator) | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_commutator_fermionMultiCreation_self` | `[n_i, c_i†] = c_i†` (number / creation commutator, dual via adjoint) | `Fermion/JordanWigner.lean` |
| `spinHalfOpMinus_mul_spinHalfOpPlus_commute_pauliZ` | matrix identity: `Commute (σ^- σ^+) σ^z` (both diagonal in the computational basis) | `Quantum/SpinHalfBasis.lean` |
| `fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne` | `Commute (n_i) (c_j)` for `i ≠ j` — the number operator at site `i` commutes with any annihilation at a different site, via the `n σ^z = σ^z n` matrix commutativity absorbing the JW-string `σ^z_i` factor | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_commute_fermionMultiCreation_of_ne` | dual: `Commute (n_i) (c_j†)` for `i ≠ j` via adjoint | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_commutator_fermionMultiAnnihilation` | `[N̂, c_j] = -c_j` — the total particle-number operator shifts annihilation down by one (sum of diagonal `[n_j, c_j] = -c_j` with vanishing off-diagonal terms) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_commutator_fermionMultiCreation` | dual: `[N̂, c_j†] = c_j†` (via adjoint) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_commute_hopping` | `Commute N̂ (c_i† · c_j)` — the hopping operator preserves total particle number (shifts cancel: `[N̂, c_i†] = c_i†` and `[N̂, c_j] = -c_j`) | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_commute_fermionTotalNumber` | `Commute (n_i) (N̂)` — site occupation commutes with the total particle number (sum of pairwise commuting `[n_i, n_j] = 0`) | `Fermion/JordanWigner.lean` |
| `fermionDensityDensity_commute_fermionTotalNumber` | `Commute (n_i · n_j) (N̂)` — the density-density operator preserves total particle number, foundational for Hubbard-style on-site interactions | `Fermion/JordanWigner.lean` |
| `fermionHopping`, `fermionHopping_commute_fermionTotalNumber` | the general single-particle hopping `H_hop = Σ_{i,j} t_{i,j} c_i† c_j` and the proof that it commutes with `N̂` (charge conservation of the kinetic Hamiltonian) | `Fermion/JordanWigner.lean` |
| `fermionDensityInteraction`, `fermionDensityInteraction_commute_fermionTotalNumber` | the general density–density interaction `V_int = Σ_{i,j} V_{i,j} n_i n_j` and the proof that it commutes with `N̂` (paired with `H_hop` this gives charge conservation for any Hubbard-type Hamiltonian) | `Fermion/JordanWigner.lean` |
| `fermionGenericHamiltonian`, `fermionGenericHamiltonian_commute_fermionTotalNumber` | the canonical charge-conserving fermion Hamiltonian `H = H_hop + V_int` and the proof that `[H, N̂] = 0`, the unified statement of charge conservation for single-species Hubbard / extended Hubbard models | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_mul_isHermitian` | `(n_i · n_j)` is Hermitian for any sites (commuting Hermitian factors) | `Fermion/JordanWigner.lean` |
| `fermionDensityInteraction_isHermitian` | `V_int = Σ V_{ij} n_i n_j` is Hermitian when every coupling entry is real (`star V_{ij} = V_{ij}`) | `Fermion/JordanWigner.lean` |
| `fermionHoppingTerm_conjTranspose` | `(c_i† · c_j)ᴴ = c_j† · c_i` (single hopping term) | `Fermion/JordanWigner.lean` |
| `fermionHopping_isHermitian` | `H_hop = Σ t_{ij} c_i† c_j` is Hermitian when `t` is Hermitian (`star (t i j) = t j i`); proved via term-wise conjTranspose + `Finset.sum_comm` for the index swap | `Fermion/JordanWigner.lean` |
| `fermionGenericHamiltonian_isHermitian` | `H = H_hop + V_int` is Hermitian when `t` is Hermitian and `V` is entry-wise real; one-line corollary of the two summand Hermiticities via `Matrix.IsHermitian.add` | `Fermion/JordanWigner.lean` |

## Open items / axioms

The following Tasaki §2.1 / §2.2 items are **not yet fully proved**.
They are tracked here so that future PRs can pick them up and replace
each axiom by a proof (or fill in the deferred construction).

### TODO (P1d''') — Problem 2.1.a for general `S ≥ 1`

**Statement (Tasaki p.15)**: For any spin `S`, every operator on the
single-site Hilbert space `h_0 = ℂ^{2S+1}` (i.e. every `(2S+1) × (2S+1)`
matrix) can be written as a polynomial in `1̂, Ŝ^(1), Ŝ^(2), Ŝ^(3)`.

**Status**: `S = 1/2` case is `pauliBasis` (P1d''). `S = 1` case is now
done via `Quantum/SpinOneDecomp.lean` (`spinOneProj{Plus,Zero,Minus}_eq_polynomial`,
`spinOneUnit*_eq_polynomial`, `spinOne_decomposition`), following
Tasaki solution S.1: diagonal projectors via Lagrange interpolation in
`Ŝ^(3)`, off-diagonals via `Ŝ^±`, spanning theorem. The general
`S ≥ 1` case requires generic `Fin (2S+1)` typing and a polymorphic
Lagrange interpolation infrastructure; not started.

### ~~TODO — Tasaki Problem 2.2.c (SU(2) non-invariance / averaged state)~~ **DONE**

**Statement (Tasaki p.23, eq. (2.2.15))**: An explicit averaged state
of the form

```
(1/4π) ∫₀^{2π} dφ ∫₀^π dθ sin θ · Û^(3)_φ · Û^(2)_θ · |↑₁⟩|↓₂⟩
```

equals (up to phase) the singlet `(1/√2)(|↑₁⟩|↓₂⟩ - |↓₁⟩|↑₂⟩)`. The
problem asks to verify this and to characterize states that fail to be
SU(2)-invariant.

**Status**: Formally proved with zero `sorry` in `Quantum/SU2Integral.lean`
as `problem_2_2_c`. The proof integrates over the Euler-angle parameter space
using `integral_cexp_I_mul_zero_two_pi`, `integral_cexp_neg_I_mul_zero_two_pi`,
and the half-angle trig integrals established in earlier PRs. See
`Quantum/SpinHalfRotation.lean` for `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown`
and `Quantum/SU2Integral.lean` for all supporting lemmas.

## Links

- [API documentation (doc-gen4)](docs/)
- [GitHub repository](https://github.com/phasetr/lattice-system)
- [Mathematical guide (`tex/proof-guide.tex`)](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex)
- [ising-model (upstream project)](https://github.com/phasetr/ising-model)
- [Lean by Example](https://lean-ja.github.io/lean-by-example/)
