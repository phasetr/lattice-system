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

## Refactoring conventions and review criteria

A **single-source-of-truth document** for refactoring conventions
applied as the review checklist on every pull request:
[Refactoring conventions and review criteria](refactoring-conventions.html).
Topics: test methods (decide / bridge / small-exhaustive / shim /
`#guard_msgs`), module-split criteria, generic / dedup conventions,
deprecation window policy, naming / docstring rules, linter
exceptions, public-doc synchronisation.

The companion page [Deprecation window](deprecations.html) tracks
currently-deprecated public declarations, the `since` date,
recommended replacement, and earliest-removal window.

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
| P1d''' (Tasaki §2.1) | Problem 2.1.a for `S ≥ 1` (polynomial basis of `M_{2S+1}(ℂ)` via Lagrange interpolation in `Ŝ^(3)` and `Ŝ^±` ladder action) | Done for `S = 1`; general `S ≥ 1` (`Fin (2S+1)` abstraction) **In progress (Issue #458)** — β-1 (operators on `Fin (N + 1)` with `N = 2S`) underway; β-2 (SU(2) commutator algebra), β-3 (Lagrange interpolation), β-4 (off-diagonal units), β-5 (spanning) follow |
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
| P1j (Tasaki §2.3) | Single-spin and multi-spin time-reversal map `Θ̂ := û_2 · K̂` for `S = 1/2`: explicit formula `Θ̂((a, b)ᵀ) = (-b*, a*)ᵀ` (Tasaki eq. (2.3.6)), action on `|ψ^↑⟩` / `|ψ^↓⟩`, additivity, antilinearity, single-spin **Kramers degeneracy** `Θ̂² = -1̂` (Tasaki eq. (2.3.8) at half-odd-integer spin), spin sign flip `Θ̂(Ŝ^(α) v) = -Ŝ^(α)(Θ̂ v)` (Tasaki eq. (2.3.14)), and multi-spin Kramers `Θ̂_tot² = (-1)^|Λ| · 1̂` for finite `Λ` (Tasaki §2.3 lattice extension at `S = 1/2`) | Done |
| P1k (Tasaki §2.5) | Antiferromagnetic Néel state on bipartite chain `Fin (2K)` / 2D `Fin (2K) × Fin (2L)` / 3D `(Fin (2K) × Fin (2L)) × Fin (2M)`: state definitions, magnetisation = 0, ∈ `H_0`, per-bond `Ŝ_x · Ŝ_y · |Φ_Néel⟩ = (1/2)|swap⟩ - (1/4)|Φ_Néel⟩` for every adjacent and wrap-around bond (Tasaki §2.5 (2.5.3)), per-bond expectation `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = -(1/4)` (Tasaki §2.5 (2.5.4) ingredient), per-bond `Ŝ^z · Ŝ^z` correlation `-(1/4)` and off-diagonal correlator vanishing, parallel-bond expectation `+1/4`, K=1 chain Heisenberg energy `J/2`, time-reversal `Θ̂_tot · |Φ_Néel⟩` action across all dimensions, Marshall sign machinery (generic `marshallSignOf` + chain / 2D / 3D specialisations + `flipConfig` + Marshall × time-reversal bridge), the **generic graph-centric `neelStateOf : (V → Bool) → ((V → Fin 2) → ℂ)`** primitive (Tasaki §2.5 (2.5.2) graph-centric form) of which the chain / 2D / 3D versions are 1-line corollaries via the `_eq_neelConfigOf` / `_eq_neelStateOf` bridges, the **Marshall-dressed standard basis** `marshallDressedBasis A σ := marshallSignOf A σ • basisVec σ` (Tasaki §2.5 (2.5.8)) with orthonormality and `H_M`-membership, the **realness of dressed Heisenberg matrix elements** for real coupling `J` (Tasaki §2.5 p. 41, Property (i): each `((spinHalfDot x y) σ σ').im = 0`, hence `((heisenbergHamiltonian J) σ σ').im = 0`, hence the dressed bilinear pairing has zero imaginary part), the **Marshall sign trick** (Tasaki §2.5 p. 41, Property (ii)): for real non-negative `J` supported on bipartite bonds and `σ ≠ σ'`, the dressed off-diagonal Heisenberg pairing has non-positive real part, the **swap-connectivity** (Tasaki §2.5 p. 41–42, Property (iii)): for a connected graph `G` and any `σ x ≠ σ y`, the configurations `σ` and `basisSwap σ x y` are connected by a chain of single-edge swaps, and the **Marshall–Lieb–Mattis Theorem 2.2 in `H_0` (matrix level)**: assembled across PRs α-5a through α-5o, the shifted dressed Heisenberg matrix `B = c · I − M` (symmetric, non-negative, irreducible on `H_0`) admits a unique-up-to-positive-scalar strictly positive Perron–Frobenius eigenvector — equivalent to the matrix-level Tasaki (2.5.4) ground-state expansion `Σ_σ c_σ \|Ψ̃^σ⟩` with `c_σ > 0` — first five steps of the Marshall–Lieb–Mattis Theorem 2.2 formalization track (Issue #412) | In progress |
| P1l (Tasaki §2.5, 2D / 3D Heisenberg) | 2D square-lattice + 2D torus + 3D cubic-lattice Heisenberg Hamiltonians via graph products `pathGraph (N+1) □ pathGraph (N+1)` and `cycleGraph (N+2) □ cycleGraph (N+2)`; Hermiticity + Gibbs state companion families (full 11-companion family per variant: `_isHermitian`, `_commute_hamiltonian`, `_GibbsExpectation_zero`, `_im_of_isHermitian`, `_commutator_hamiltonian`, `_mul_hamiltonian_im`, `_hamiltonian_sq_im`, `_hamiltonian_pow_im`, `_anticommutator_im`, `_commutator_re`, `_HamiltonianVariance_im`, `_partitionFn_im`, `_ofReal_re_eq`, `_pow_trace`) at parity with the 1D open / periodic chain | Done |
| P2 | Finite-volume Hubbard / BCS | In progress (single-mode CAR algebra; multi-mode Jordan–Wigner backbone: JW string + multi-mode `c_i`, `c_i†` definitions and Hermiticity, `c_0` reductions, full on-site CAR `c_i² = 0`, `(c_i†)² = 0`, `{c_i, c_i†} = 1`, adjoint `(c_i)ᴴ = c_i†`, JW string idempotent `J² = 1`, site-occupation number operator `n_i` with Hermiticity and idempotency; **full cross-site CAR algebra `{c_i, c_j} = 0`, `{c_i†, c_j†} = 0`, `{c_i, c_j†} = 0`, `{c_i†, c_j} = 0` for every `i < j`**; **Hubbard chain (open + periodic BC), Hermiticity + full Gibbs companion family**; **U(1)×U(1) spin symmetry: `[N_↑, H] = [N_↓, H] = [S^z_tot, H] = 0` (Tasaki §9.3.3)**; **full SU(2) spin symmetry: `[Ŝ^+_tot, H] = [Ŝ^-_tot, H] = 0` (Tasaki §9.3.3)**; **all-up-spin state `hubbardAllUpState`: complete kinetic/interaction sector; Casimir `(Ŝ_tot)²`; eigenvalue `S_max(S_max+1)`; Definition 11.1 `isSaturatedFerromagnet` (Tasaki §11.1.1 / eq. (10.1.5))**; **SU(2) algebra: `[Ŝ^z, Ŝ^-] = -Ŝ^-`, eigenvalue preservation and decrement by `Ŝ^-` (Tasaki §9.3.3, §11.1.1)**) |
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

### Spin-`S` operators (general S ≥ 0, parameterised by `N = 2S : ℕ`)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).

Generic spin-`S` operators live on `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ`, with `N = 2S : ℕ` (so `N = 1` ⇔ `S = 1/2`, `N = 2` ⇔ `S = 1`). Tracking issue #458 (Tasaki §2.1 P1d''' general-S generalisation).

| Lean name | Statement | File |
|---|---|---|
| `spinSOp3` | `Ŝ^(3) := diag(N/2, N/2 - 1, …, -N/2)` for `N : ℕ` | `Quantum/SpinS/Operators.lean` |
| `spinSOpPlus` / `spinSOpMinus` | raising/lowering operators with matrix entries `√(k·(N − k + 1))` (resp. `√((N − k)(k + 1))`) on the immediate sub/super-diagonal | `Quantum/SpinS/Operators.lean` |
| `spinSOp1` / `spinSOp2` | `Ŝ^(1) := (Ŝ^+ + Ŝ^-) / 2`, `Ŝ^(2) := (Ŝ^+ − Ŝ^-) / (2 i)` | `Quantum/SpinS/Operators.lean` |
| `spinSOp{Plus,Minus}_apply_top` / `_bottom` | `Ŝ^+` annihilates `\|N⟩` (highest weight); `Ŝ^-` annihilates `\|0⟩` (lowest weight) — the ladder boundaries | `Quantum/SpinS/Operators.lean` |
| `spinSOp3_commutator_spinSOp{Plus,Minus}` | **Cartan relations** `[Ŝ^{(3)}, Ŝ^+] = Ŝ^+` and `[Ŝ^{(3)}, Ŝ^-] = -Ŝ^-`: `Ŝ^±` shift the magnetic quantum number by `±1`. Proved entry-wise via `Matrix.diagonal_mul` / `mul_diagonal` (β-2 of Issue #458) | `Quantum/SpinS/Algebra.lean` |
| `spinSOp{Plus,Minus}_conjTranspose` / `spinSOp{1,2,3}_isHermitian` | adjointness `(Ŝ^+)ᴴ = Ŝ^-`, `(Ŝ^-)ᴴ = Ŝ^+`, and Hermiticity of `Ŝ^{(α)}` for `α ∈ {1, 2, 3}` (β-3 of Issue #458). The ladder adjointness follows from the matrix-entry symmetry; `Ŝ^{(1)}` and `Ŝ^{(2)}` use the `1/2` and `1/(2i)` self-conjugacy facts | `Quantum/SpinS/Hermitian.lean` |
| `spinSDiagProj` / `spinSOp3_sub_smul_mul_diagProj` / `_self_mul_diagProj` | the **diagonal projector** `P_k := diag(δ_{i,k})` and the eigenvalue-action lemma `(Ŝ^{(3)} − λ_j • 1) · P_k = (λ_k − λ_j) · P_k`, with the annihilation specialisation at `j = k` (β-4 of Issue #458). Foundation for the Lagrange-interpolation polynomial decomposition: each `P_k` will be expressed as `∏_{j ≠ k} (Ŝ^{(3)} − λ_j • 1) / (λ_k − λ_j)` in a follow-up PR | `Quantum/SpinS/DiagProj.lean` |
| `spinSOp3_mul_diagProj` / `diagProj_mul_spinSOp3` / `spinSOp3_commute_diagProj` | the **eigenvalue equation** `Ŝ^{(3)} · P_k = λ_k · P_k` (where `λ_k = (N : ℂ)/2 − k`), with the symmetric `P_k · Ŝ^{(3)} = λ_k · P_k` and the resulting commutativity. Both are diagonal-times-diagonal computations (β-5 of Issue #458) | `Quantum/SpinS/Lagrange.lean` |
| `mul_diagProj_apply` / `diagProj_mul_apply` / `spinSOp{Plus,Minus}_mul_diagProj_apply` | **Column/row selection** by the diagonal projector: `(A · P_k)[i, j] = A[i, k]` if `j = k` else `0` (and dually for `P_k · A`). Specialised to `Ŝ^±` produces off-diagonal matrix units (β-6 of Issue #458) — the building blocks of the polynomial decomposition theorem | `Quantum/SpinS/LadderProj.lean` |
| `spinSOpPlus_mul_diagProj_succ_mul_spinSOpMinus` | **Ladder recursion**: `Ŝ^+ · P_{k+1} · Ŝ^- = (k + 1)(N − k) · P_k`. The triple product collapses to a non-zero scalar multiple of `P_k`. Iterating from the lowest-weight projector `P_N` (itself a polynomial in `Ŝ^{(3)}`) yields every diagonal projector as a polynomial in `{1̂, Ŝ^{(α)}}` (β-7 of Issue #458) | `Quantum/SpinS/LadderRecursion.lean` |
| `spinSOpPlus_mul_diagProj_first` / `spinSOpMinus_mul_diagProj_last` | **Ladder boundaries**: `Ŝ^+ · P_0 = 0` (top of ladder) and `Ŝ^- · P_N = 0` (bottom). The first/last columns of `Ŝ^±` vanish, so multiplication by `P_{0/N}` (which selects that column) gives `0`. Terminate the recursion at the highest- and lowest-weight projectors (β-8 of Issue #458) | `Quantum/SpinS/LadderBoundary.lean` |
| `spinSDiagProj_isHermitian` / `sum_spinSDiagProj_eq_one` | **Hermiticity** of each `P_k`, and the **resolution of the identity** `Σ_k P_k = 1`. The latter is the cornerstone for the matrix-unit decomposition: combined with the off-diagonal matrix units (β-6, β-7), gives every matrix in `M_{N+1}(ℂ)` (β-9 of Issue #458) | `Quantum/SpinS/DiagProjProperties.lean` |
| `spinSOpPlus_mul_diagProj_succ_eq_single` / `spinSOpMinus_mul_diagProj_eq_single` | **Off-diagonal matrix-unit decomposition**: `Ŝ^+ · P_{i+1} = √((i+1)(N−i)) · E_{i, i+1}` and `Ŝ^- · P_i = √((N−i)(i+1)) · E_{i+1, i}`, where `E_{a, b} := Matrix.single a b 1` is the (a, b) matrix unit (β-10 of Issue #458). These are the simplest off-diagonal matrix units expressible via `Ŝ^±` ladder action on diagonal projectors | `Quantum/SpinS/OffDiagUnit.lean` |
| `spinSOp3_sq_eq_diagonal` | `(Ŝ^{(3)})² = diag((N/2 − i)²)`. Step toward the **Casimir identity** `(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1` for general spin (β-11 of Issue #458) | `Quantum/SpinS/Op3Square.lean` |
| `spinSOpPlus_mul_spinSOpMinus_eq_diagonal` | `Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))`. The product is diagonal because `Ŝ^+[i, l] · Ŝ^-[l, j]` is non-zero only when `l = i + 1 = j + 1`, forcing `i = j`. Combined with the analogous `Ŝ^- · Ŝ^+` and `(Ŝ^{(3)})²`, this assembles the Casimir identity (β-12 of Issue #458) | `Quantum/SpinS/PlusMinusDiag.lean` |
| `spinSOpMinus_mul_spinSOpPlus_eq_diagonal` | `Ŝ^- · Ŝ^+ = diag(i · (N − i + 1))`. Symmetric to β-12 with `Ŝ^±` swapped (β-13 of Issue #458) | `Quantum/SpinS/MinusPlusDiag.lean` |
| `spinSOp1_sq_add_spinSOp2_sq` / `spinSOp_total_squared` | **Casimir identity** for general spin-`S`: `(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1`, equivalent to `S(S+1) · 1` for `S = N/2`. Proves the irreducible spin-`S` representation has Casimir eigenvalue `S(S+1)` (Schur's lemma). The intermediate identity `(Ŝ^{(1)})² + (Ŝ^{(2)})² = (1/2)(Ŝ^+ · Ŝ^- + Ŝ^- · Ŝ^+)` is proved using `module` (β-14 of Issue #458) | `Quantum/SpinS/Casimir.lean` |
| `spinSOp3_mulVec_basis` | spin-`S` eigenstate equation `Ŝ^{(3)} · \|k⟩ = (N/2 − k) · \|k⟩`, where `\|k⟩ := Pi.single k 1` is the `k`-th unit basis vector of `(Fin (N + 1) → ℂ)` (β-15 of Issue #458) | `Quantum/SpinS/Eigenstates.lean` |

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

### Time-reversal map for `S = 1/2` (Tasaki §2.3)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.3 eqs. (2.3.4)–(2.3.8), pp. 26–27.

| Lean name | Statement | File |
|---|---|---|
| `timeReversalSpinHalf` | `Θ̂(v) = (-conj(v 1), conj(v 0))` (Tasaki eq. (2.3.6), `S = 1/2`); the antilinear unitary `û_2 · K̂` of §2.3 | `Quantum/TimeReversalSpinHalf.lean` |
| `timeReversalSpinHalf_spinHalfUp` / `_spinHalfDown` | `Θ̂|ψ^↑⟩ = |ψ^↓⟩` and `Θ̂|ψ^↓⟩ = -|ψ^↑⟩` | `Quantum/TimeReversalSpinHalf.lean` |
| `timeReversalSpinHalf_add` | additivity `Θ̂(v + w) = Θ̂(v) + Θ̂(w)` | `Quantum/TimeReversalSpinHalf.lean` |
| `timeReversalSpinHalf_smul` | **antilinearity** in the scalar: `Θ̂(c • v) = (conj c) • Θ̂(v)` (Tasaki §2.3 antilinearity warning, pp. 26–27) | `Quantum/TimeReversalSpinHalf.lean` |
| `timeReversalSpinHalf_sq` | **Kramers degeneracy at `S = 1/2`** (Tasaki eq. (2.3.8), half-odd-integer): `Θ̂² = -1̂` | `Quantum/TimeReversalSpinHalf.lean` |
| `timeReversalSpinHalf_spinHalfOp{1,2,3}_mulVec` | spin sign flip (Tasaki eq. (2.3.14)): `Θ̂(Ŝ^(α) · v) = (-Ŝ^(α)) · (Θ̂ v)` for `α = 1, 2, 3` — equivariance form of `Θ̂ Ŝ^(α) Θ̂⁻¹ = -Ŝ^(α)` | `Quantum/TimeReversalSpinHalf.lean` |
| `complexConjugationSpinHalf` | the antilinear complex-conjugation map `K̂` of Tasaki §2.3 eq. (2.3.4) at `S = 1/2`: `K̂(v) i := conj(v i)` | `Quantum/TimeReversalSpinHalf.lean` |
| `complexConjugationSpinHalf_sq` / `_add` / `_smul` | `K̂` is involutive (`K̂² = id`), additive, and antilinear in the scalar | `Quantum/TimeReversalSpinHalf.lean` |
| `timeReversalSpinHalf_eq_spinHalfRot2_pi_mulVec` | the **factorisation identity** of Tasaki §2.3: `Θ̂ = û_2 · K̂` where `û_2 = spinHalfRot2 π` is the π rotation about the `2`-axis | `Quantum/TimeReversalSpinHalf.lean` |
| `flipConfig` / `flipConfig_apply` / `flipConfig_involutive` | the spin-flip on a many-body configuration `σ : Λ → Fin 2`: `flipConfig σ x := 1 - σ x`; involutive | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSign` / `timeReversalSign_zero` / `_one` / `_mul_flip` | per-site sign factor `ε(0) = 1`, `ε(1) = -1` for the multi-spin time-reversal, with `ε(s) · ε(1 - s) = -1` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti` | multi-spin time-reversal map (Tasaki §2.3 lattice extension, `S = 1/2`): `(Θ̂_tot v) τ := (∏_x ε(τ x)) · conj(v (flip τ))` for finite `Λ` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSign_prod_conj` / `timeReversalSign_prod_mul_flip` | the product `∏_x ε(τ x)` is real (conjugation invariant); the cross product equals `(-1)^|Λ|` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_sq` | **Multi-spin Kramers degeneracy at `S = 1/2`** (Tasaki §2.3 half-odd-integer extension): `Θ̂_tot² = (-1)^|Λ| · 1̂` — `+1̂` when `|Λ|` is even, `-1̂` when odd | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_basisVec` | action of `Θ̂_tot` on a many-body basis state: `Θ̂_tot |Ψ_σ⟩ = (∏_x ε(flip σ x)) · |Ψ_{flip σ}⟩` — natural many-body generalisation of `Θ̂|↑⟩ = |↓⟩` and `Θ̂|↓⟩ = -|↑⟩` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_onSite_pauliZ_mulVec` | multi-site sign-flip equivariance for `σ^z` (Tasaki §2.3 (2.3.14) lifted to many-body): `Θ̂_tot ((onSite x σ^z) v) = (-(onSite x σ^z))(Θ̂_tot v)`. Diagonal-action case; `σ^x`, `σ^y` deferred | `Quantum/TimeReversalMulti.lean` |
| `siteFlipAt` / `siteFlipAt_self` / `siteFlipAt_of_ne` / `flipConfig_siteFlipAt_comm` / `siteFlipAt_involutive` | per-site flip helpers: `siteFlipAt τ x` flips slot `x` only; commutes with `flipConfig`; involutive. The combinatorial primitive underlying off-diagonal `σ^x_x` / `σ^y_x` action (deferred) | `Quantum/TimeReversalMulti.lean` |
| `onSite_pauliX_mulVec_basisVec` | basis-state action of the off-diagonal site Pauli: `(onSite x σ^x).mulVec |Ψ_σ⟩ = |Ψ_{siteFlipAt σ x}⟩` (the spin at site `x` is swapped) | `Quantum/TimeReversalMulti.lean` |
| `pauliX_eq_indicator` / `onSite_pauliX_mulVec_apply` | closed-form `pauliX a b = if b = 1 - a then 1 else 0`, lifted to `((onSite x σ^x).mulVec v) τ = v (siteFlipAt τ x)` for any state `v` (general extension of the basis-state action) | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSign_prod_siteFlipAt` | `∏_y ε((siteFlipAt τ x) y) = -(∏_y ε(τ y))` — the per-site flip swaps `ε(τ x)` with `ε(1 - τ x) = -ε(τ x)`, flipping the total sign | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_onSite_pauliX_mulVec` | multi-site sign-flip equivariance for `σ^x` (Tasaki §2.3 (2.3.14) at α = 1): `Θ̂_tot ((onSite x σ^x) v) = (-(onSite x σ^x))(Θ̂_tot v)` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_onSite_pauliY_mulVec` | multi-site sign-flip equivariance for `σ^y` (Tasaki §2.3 (2.3.14) at α = 2): `Θ̂_tot ((onSite x σ^y) v) = (-(onSite x σ^y))(Θ̂_tot v)`. The proof handles the per-site `±i` factor via `conj(pauliY_sign(1 - s)) = pauliY_sign(s)` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_add` / `_smul` / `_real_smul` | multi-spin `Θ̂_tot` is additive, antilinear in the scalar (`Θ̂_tot(c • v) = conj(c) • Θ̂_tot v`), and real-linear (special case of antilinearity at real `r`) — foundational for lifting Pauli-axis equivariance to bilinear / Heisenberg-type Hamiltonian forms | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_onSite_spinHalfOp{1,2,3}_mulVec` | Tasaki §2.3 (2.3.14) for spin-1/2 ops `Ŝ^(α) = σ^(α) / 2`: `Θ̂_tot ((onSite x Ŝ^(α)) v) = (-(onSite x Ŝ^(α)))(Θ̂_tot v)` for α = 1, 2, 3 — direct corollaries of the Pauli versions by scalar (1/2) multiplication | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_spinHalfDot_mulVec` | **Time-reversal invariance of the bilinear `Ŝ_x · Ŝ_y`** (Tasaki §2.3): `Θ̂_tot ((Ŝ_x · Ŝ_y) v) = (Ŝ_x · Ŝ_y)(Θ̂_tot v)` — two equivariance `-1` factors cancel; sums per-axis | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec` | **Time-reversal invariance of the Heisenberg Hamiltonian** (Tasaki §2.3): for real coupling `J` (`conj(J(x,y)) = J(x,y)`), `Θ̂_tot ((H J) v) = (H J)(Θ̂_tot v)`. Combines per-bond invariance + Θ̂_tot antilinearity (J reality) + additivity (over double-sum) | `Quantum/TimeReversalMulti.lean` |
| `openChainCoupling_conj` / `periodicChainCoupling_conj` | every entry of `openChainCoupling N J` (resp. `periodicChainCoupling N J`) is real (under complex conjugation), since `J : ℝ` makes `(-(J : ℂ))` real-valued | `Quantum/HeisenbergChain.lean` |
| `timeReversalSpinHalfMulti_openChainHeisenberg_mulVec` / `_periodicChainHeisenberg_mulVec` / `_squareLatticeHeisenberg_mulVec` / `_squareTorusHeisenberg_mulVec` / `_cubicLatticeHeisenberg_mulVec` | concrete time-reversal invariance: the open / periodic chain, the 2D open square / torus, and the 3D cubic Heisenberg Hamiltonians all commute with `Θ̂_tot` for any real coupling `J : ℝ`. Backed by `*Coupling_conj` reality lemmas in `HeisenbergChain.lean` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_basisVec_upDown` / `_basisVec_basisSwap_upDown` | `Θ̂_tot |↑↓⟩ = -|↓↑⟩` and `Θ̂_tot |↓↑⟩ = -|↑↓⟩` on `Fin 2` | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_singlet` | the two-site spin singlet `|↑↓⟩ - |↓↑⟩` is **time-reversal invariant** (Tasaki §2.3 / §A.3): being the SU(2) `S = 0` representation, it survives `Θ̂_tot` unchanged | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_triplet_zero` | the triplet `m = 0` state `|↑↓⟩ + |↓↑⟩` is **anti-invariant** under `Θ̂_tot`: `Θ̂_tot (|↑↓⟩ + |↓↑⟩) = -(|↑↓⟩ + |↓↑⟩)` (the symmetric combination picks up a minus sign from the per-basis-vector flip) | `Quantum/TimeReversalMulti.lean` |

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
| `neelChainConfig` / `neelChainState` | Tasaki §2.5 eq. (2.5.2) Néel state at `S = 1/2` on the parity-coloured chain `Fin (2 * K)`: `σ(i) = ↑` if `i.val` even, `↓` if odd | `Quantum/NeelState.lean` |
| `neelChainConfig_magnetization_zero` / `neelChainState_mem_magnetizationSubspace_zero` | the Néel chain configuration has total magnetisation `0`, so the corresponding basis state lies in the `Ŝ_tot^(3) = 0` eigenspace `H_0` | `Quantum/NeelState.lean` |
| `heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero` | for any coupling `J`, `H · |Φ_Néel⟩` again lies in `H_0` — immediate corollary of SU(2) invariance applied to the Néel state. The Néel state is *not* an H-eigenstate (Tasaki §2.5 (2.5.3)), but it cannot leak into other magnetisation sectors | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelChainState_adjacent` | Tasaki §2.5 eq. (2.5.3) per-bond action: for every adjacent pair `(i, i+1)` of the chain `Fin (2 * K)`, `Ŝ_⟨i⟩ · Ŝ_⟨i+1⟩ · |Φ_Néel⟩ = (1/2) · |swap_{i,i+1} Φ_Néel⟩ - (1/4) · |Φ_Néel⟩` (antiparallel case, parity-derived) | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelChainState_wrap` | wrap-around bond `(2K + 1, 0)` action on the periodic chain `Fin (2 * (K + 1))`: same `(1/2) swap - (1/4) Néel` decomposition as the open-bond case (parities `1` and `0` differ since the cycle length is even). Together with the adjacent lemma, covers every bond of the periodic chain | `Quantum/NeelState.lean` |
| `heisenbergHamiltonian_openChainCoupling_one_mulVec_neelChainState_one` | `K = 1` instance: `H_open(N=1, J) · |Φ_Néel⟩ = -J · |↓↑⟩ + (J/2) · |Φ_Néel⟩`. Lifts the per-bond `spinHalfDot` calculation through `H_open(N=1, J) = -2J · spinHalfDot 0 1`. The non-eigenstate character of the Néel state is plain | `Quantum/NeelState.lean` |
| `neelChainConfig_one_eq_upDown` / `timeReversalSpinHalfMulti_neelChainState_one` | bridges the `K = 1` Néel chain configuration to the existing `upDown` config and computes `Θ̂_tot (neelChainState 1) = -basisVec (basisSwap upDown 0 1)` (the per-down sign convention of `Θ̂` flips the antiparallel pair) | `Quantum/NeelState.lean` |
| `neelSquareConfig` / `neelSquareState` | 2D checkerboard Néel state on `Fin (2K) × Fin (2L)` (Tasaki §2.5 (2.5.2) bipartite case): `σ(i, j) = ↑` if `(i.val + j.val) % 2 = 0`, `↓` otherwise | `Quantum/NeelState.lean` |
| `neelSquareConfig_magnetization_zero` / `neelSquareState_mem_magnetizationSubspace_zero` | the 2D Néel configuration has total magnetisation `0` and the corresponding state lies in the `Ŝ_tot^(3) = 0` eigenspace `H_0`. Proof: row-by-row column-sum vanishes (helper `sum_alternating_sign_offset` for the 1D parity sum with offset) | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelSquareState_horizontal_adjacent` / `_vertical_adjacent` | Tasaki §2.5 (2.5.3) per-bond action on the 2D Néel state for the horizontal (`(i,j)~(i+1,j)`) and vertical (`(i,j)~(i,j+1)`) nearest-neighbour bonds: same `(1/2) · |swap⟩ - (1/4) · |Φ_Néel⟩` decomposition as the 1D chain | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelSquareState_horizontal_wrap` / `_vertical_wrap` | wrap-around bond actions on the 2D torus Néel state: horizontal `((2K+1, j), (0, j))` on `Fin (2(K+1)) × Fin (2L)` and vertical `((i, 2L+1), (i, 0))` on `Fin (2K) × Fin (2(L+1))` are antiparallel (parities differ by an odd shift); both inherit the same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition. With `_horizontal_adjacent` / `_vertical_adjacent`, covers every nearest-neighbour bond of the 2D torus Néel state | `Quantum/NeelState.lean` |
| `neelCubicConfig` / `neelCubicState` / `neelCubicConfig_magnetization_zero` / `neelCubicState_mem_magnetizationSubspace_zero` | 3D cubic checkerboard Néel state on `(Fin (2K) × Fin (2L)) × Fin (2M)`: `σ((i,j),k) = ↑` if `(i+j+k) % 2 = 0`, magnetisation = 0, lies in `H_0` | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelCubicState_x_adjacent` / `_y_adjacent` / `_z_adjacent` | Tasaki §2.5 (2.5.3) per-bond actions on the 3D cubic Néel state for the three nearest-neighbour bond axes (x, y, z): same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelCubicState_x_wrap` / `_y_wrap` / `_z_wrap` | wrap-around bond actions on the 3D cubic-torus Néel state: each axis-wrap (`((2K+1, j), k) ~ ((0, j), k)`, `((i, 2L+1), k) ~ ((i, 0), k)`, `((i, j), 2M+1) ~ ((i, j), 0)`) is antiparallel (one coordinate shifts by an odd amount). All three axes inherit the same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition. With `_x_adjacent` / `_y_adjacent` / `_z_adjacent`, covers every nearest-neighbour bond of the 3D cubic torus Néel state | `Quantum/NeelState.lean` |
| `timeReversalSpinHalfMulti_neelSquareState_one_one` | concrete `K = L = 1` (2×2 = 4-site) instance: `Θ̂_tot (neelSquareState 1 1) = basisVec (flipConfig (neelSquareConfig 1 1))` (the equal up/down counts make `(-1)^|A| = 1`, so no overall sign) | `Quantum/NeelState.lean` |
| `timeReversalSpinHalfMulti_neelCubicState_one_one_one` | concrete `K = L = M = 1` (2×2×2 = 8-site) instance: `Θ̂_tot (neelCubicState 1 1 1) = basisVec (flipConfig (neelCubicConfig 1 1 1))` (4 down spins after flipping → `(-1)^4 = 1`, so no overall sign) | `Quantum/NeelState.lean` |
| `timeReversalSpinHalfMulti_neelChainState` | general-`K` 1D chain: `Θ̂_tot (neelChainState K) = (-1)^K · basisVec (flipConfig (neelChainConfig K))` (helper `prod_alternating_neg_one` collapses the per-site sign product). Specialisations at K=1 (factor −1), K=2 (factor 1), K=3 (factor −1) provided as tests | `Quantum/NeelState.lean` |
| `timeReversalSpinHalfMulti_neelSquareState` | general-`K, L` 2D checkerboard: `Θ̂_tot (neelSquareState K L) = basisVec (flipConfig (neelSquareConfig K L))` (no sign because `(-1)^(2KL) = 1`). Helper `prod_alternating_neg_one_offset` reduces the parity-shifted column product to `(-1)^L`, then the row product `((-1)^L)^(2K) = 1` | `Quantum/NeelState.lean` |
| `timeReversalSpinHalfMulti_neelCubicState` | general-`K, L, M` 3D cubic checkerboard: `Θ̂_tot (neelCubicState K L M) = basisVec (flipConfig (neelCubicConfig K L M))` (no sign because `(-1)^(4KLM) = 1`). Reduces along `k`-axis to `(-1)^M` then collapses the `(2K)·(2L)`-fold product | `Quantum/NeelState.lean` |
| `basisVec_apply` / `basisVec_self` / `basisVec_of_ne` | foundational evaluation lemmas for the standard basis vectors: explicit `if`-form, diagonal `=1`, and off-diagonal `=0` | `Quantum/ManyBody.lean` |
| `sum_mul_basisVec` / `basisVec_sum_mul` | selector-sum identities `∑ τ, f τ · basisVec σ τ = f σ` (and the symmetric form), the workhorses for inner-product computations on the spin Hilbert space | `Quantum/ManyBody.lean` |
| `basisVec_inner` | basis-vector orthonormality `∑ τ, basisVec σ τ · basisVec ρ τ = if ρ = σ then 1 else 0`. Real bilinear pairing (no complex conjugation needed since `basisVec` values are 0 or 1) | `Quantum/ManyBody.lean` |
| `basisSwap_ne_self` | `σ x ≠ σ y → basisSwap σ x y ≠ σ` (the swap of an antiparallel pair changes the configuration). Useful for orthogonality computations on swapped states | `Quantum/SpinDot.lean` |
| `neelChainState_norm_squared` / `neelSquareState_norm_squared` / `neelCubicState_norm_squared` | the 1D / 2D / 3D Néel states are normalized: `∑ τ, |Φ_Néel(τ)|² = 1` (one-line consequence of `basisVec_inner`) | `Quantum/NeelState.lean` |
| `neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero` | the Néel chain state is orthogonal to the swapped basis vector at any adjacent (antiparallel) bond: `∑ τ, Φ_Néel(τ) · basisVec(swap)(τ) = 0`. Direct consequence of `basisVec_inner` + `basisSwap_ne_self` | `Quantum/NeelState.lean` |
| `neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter` | the per-adjacent-bond expectation `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = -1/4` (Tasaki §2.5 (2.5.4) ingredient at S = 1/2). Combines `spinHalfDot_mulVec_neelChainState_adjacent` (bond action) with the orthogonality + norm² lemmas to compute `(1/2)·0 - (1/4)·1 = -1/4` | `Quantum/NeelState.lean` |
| `inner_basisVec_spinHalfDot_basisVec_antiparallel` | generic lemma: for any antiparallel `(x, y)` configuration `σ`, `⟨basisVec σ, Ŝ_x · Ŝ_y · basisVec σ⟩ = -1/4`. The 1-line foundation for every Néel-bond expectation | `Quantum/SpinDot.lean` |
| `inner_basisVec_spinHalfDot_basisVec_parallel` | parallel companion: for `σ x = σ y` (and `x ≠ y`), `⟨basisVec σ, Ŝ_x · Ŝ_y · basisVec σ⟩ = +1/4`. Both basis vectors at the parallel pair are eigenvectors of `Ŝ_x · Ŝ_y` (eigenvalue `+1/4`) | `Quantum/SpinDot.lean` |
| `neelChainState_inner_spinHalfDot_parallel_eq_one_quarter` | Néel chain same-sublattice (parallel) bond expectation `+1/4`: for any `x ≠ y` with `x.val % 2 = y.val % 2` (e.g., `(0, 2)`, `(1, 3)`), `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = +1/4` | `Quantum/NeelState.lean` |
| `onSite_spinHalfOp3_mul_onSite_spinHalfOp3_mulVec_basisVec` | `(Ŝ^(3)_x · Ŝ^(3)_y) · basisVec σ = (spinHalfSign σ x · spinHalfSign σ y) · basisVec σ`: every basis vector is an eigenvector of the diagonal `Ŝ^z·Ŝ^z` correlator. Composes the single-site action `Ŝ^(3)_x · |σ⟩ = ε_x · |σ⟩` twice | `Quantum/SpinDot.lean` |
| `inner_basisVec_szsz_basisVec` | generic `⟨basisVec σ, Ŝ^(3)_x · Ŝ^(3)_y · basisVec σ⟩ = spinHalfSign σ x · spinHalfSign σ y`. The diagonal-only spin-spin correlator on a basis state | `Quantum/SpinDot.lean` |
| `spinHalfSign_mul_antiparallel` | for antiparallel `s ≠ t : Fin 2`, `spinHalfSign s · spinHalfSign t = -(1/4)`. Made public in PR #332 to power the generic `inner_neelStateOf_szsz_neelStateOf_antiparallel = -(1/4)` Néel correlator | `Quantum/SpinDot.lean` |
| `inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel` | generic off-diagonal correlator: for any antiparallel `(x, y)` configuration `σ`, `⟨basisVec σ, (Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y) · basisVec σ⟩ = 0`. The off-diagonal `(Ŝ^x·Ŝ^x + Ŝ^y·Ŝ^y)` part is entirely supported on swap states (⟂ to the original) | `Quantum/SpinDot.lean` |
| `neelChainState_inner_off_diagonal_correlator_adjacent_eq_zero` | the per-adjacent-bond off-diagonal correlator on the Néel chain vanishes: `⟨Φ_Néel, (Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y) · Φ_Néel⟩ = 0`. Direct application of the generic helper | `Quantum/NeelState.lean` |
| `neelChainState_inner_szsz_adjacent_eq_neg_one_quarter` | per-adjacent-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation on the Néel chain: `-1/4`. Matches the full `Ŝ_x · Ŝ_y` expectation since the off-diagonal `Ŝ^x·Ŝ^x + Ŝ^y·Ŝ^y` parts vanish on the diagonal (they map `|σ⟩` to `|swap σ⟩ ⊥ |σ⟩`) | `Quantum/NeelState.lean` |
| `neelChainState_inner_szsz_wrap_eq_neg_one_quarter` | 1D Néel periodic chain: per-wrap-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation `-1/4` | `Quantum/NeelState.lean` |
| `neelSquareState_inner_szsz_{horizontal,vertical}_{adjacent,wrap}_eq_neg_one_quarter` | 2D Néel: per-bond `Ŝ^(3)·Ŝ^(3)` correlation `-1/4` for every horizontal / vertical adjacent and wrap bond | `Quantum/NeelState.lean` |
| `neelCubicState_inner_szsz_{x,y,z}_{adjacent,wrap}_eq_neg_one_quarter` | 3D Néel: per-bond `Ŝ^(3)·Ŝ^(3)` correlation `-1/4` for every x / y / z adjacent and wrap bond. Completes the `Ŝ^z·Ŝ^z` correlation coverage parity with the full `Ŝ·Ŝ` family from #273 | `Quantum/NeelState.lean` |
| `neelChainState_inner_spinHalfDot_wrap_eq_neg_one_quarter` | 1D wrap-bond expectation `-1/4` on the periodic Néel chain `Fin (2(K+1))` | `Quantum/NeelState.lean` |
| `neelSquareState_inner_spinHalfDot_horizontal_adjacent_eq_neg_one_quarter` / `_vertical_adjacent_` / `_horizontal_wrap_` / `_vertical_wrap_` | 2D Néel: per-bond expectation `-1/4` for every horizontal / vertical adjacent and wrap bond | `Quantum/NeelState.lean` |
| `neelCubicState_inner_spinHalfDot_{x,y,z}_adjacent_eq_neg_one_quarter` / `_{x,y,z}_wrap_` | 3D Néel: per-bond expectation `-1/4` for every x / y / z adjacent and wrap bond. With the 1D / 2D family this completes per-bond `-1/4` coverage across the full Néel-state bond family of #251 / #261 / #262 | `Quantum/NeelState.lean` |
| `neelChainState_energy_expectation_K1` | `K = 1` (2-site) open-chain Heisenberg energy expectation `⟨Φ_Néel, H_open · Φ_Néel⟩ = J/2`. Combines `openChainHeisenbergHamiltonian_two_site_eq` (`H = -2J · spinHalfDot 0 1`) with the per-bond `-1/4` expectation, giving `-2J · (-1/4) = J/2` | `Quantum/NeelState.lean` |
| `neelConfigOf` / `neelStateOf` | generic graph-centric Néel state from a sublattice indicator `A : V → Bool`: `neelConfigOf A x := if A x then ↑ else ↓` and `neelStateOf A := basisVec (neelConfigOf A)`. The chain / 2D / 3D `neelXyzConfig` / `neelXyzState` definitions are bridged via `_eq_neelConfigOf` / `_eq_neelStateOf`. Tasaki §2.5 eq. (2.5.2) graph-centric form | `Quantum/NeelState.lean` |
| `spinHalfDot_mulVec_neelStateOf_antiparallel` | generic per-bond `Ŝ_x · Ŝ_y` action on the canonical Néel state: for any `x ≠ y` with `A x ≠ A y`, `Ŝ_x · Ŝ_y · Φ_Néel(A) = (1/2) · |swap_{x, y} Φ_Néel(A)⟩ - (1/4) · Φ_Néel(A)`. Tasaki §2.5 eq. (2.5.3) graph-centric form. The chain / 2D / 3D `_adjacent` / `_wrap` bond actions are 1-line corollaries via the `_eq_neelStateOf` bridges | `Quantum/NeelState.lean` |
| `inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel` | generic per-bond `Ŝ_x · Ŝ_y` expectation on the canonical Néel state: for any `x ≠ y` with `A x ≠ A y`, `⟨Φ_Néel(A), Ŝ_x · Ŝ_y · Φ_Néel(A)⟩ = -(1/4)`. Tasaki §2.5 (2.5.4) ingredient (graph-centric form). The chain / 2D / 3D `_eq_neg_one_quarter` companions reduce to this via the `_eq_neelStateOf` bridges | `Quantum/NeelState.lean` |
| `inner_neelStateOf_szsz_neelStateOf_antiparallel` | generic per-bond `Ŝ^z_x · Ŝ^z_y` correlation on the canonical Néel state: for any `A x ≠ A y`, `⟨Φ_Néel(A), Ŝ^z_x · Ŝ^z_y · Φ_Néel(A)⟩ = -(1/4)`. Diagonal half of Tasaki §2.5 (2.5.4) | `Quantum/NeelState.lean` |
| `marshallSignOf` | generic graph-centric Marshall sign `∏_{x ∈ A} (-1)^(σ x)` for any finite vertex type `V`, sublattice indicator `A : V → Bool`, and configuration `σ : V → Fin 2`. Aligns with the project-wide graph-centric design (CLAUDE.local.md) | `Quantum/NeelState.lean` |
| `marshallSignOf_const_zero` | for any sublattice indicator `A`, the all-up Marshall sign is `marshallSignOf A (const 0) = 1`. Generic counterpart of `marshallSignChainConfig_const_zero` etc.; those are now 1-line corollaries via the `_eq_marshallSignOf` bridges | `Quantum/NeelState.lean` |
| `marshallSignChainConfig` / `marshallSignChainConfig_neelChainConfig` | the Marshall sign `(-1)^(N_A^↓)` for spin-1/2 configurations on the parity-coloured chain `Fin (2K)`, encoded as `∏_{x even} (-1)^(σ x)`; specialisation to the Néel configuration gives sign `+1` (no down spins on sublattice `A`). Foundational definition for the Marshall basis change underpinning the Marshall-Lieb-Mattis theorem (Tasaki §2.5). **Deprecated** as of 2026-04-22 in favour of the generic `marshallSignOf` (the chain / 2D / 3D Marshall sign defs are kept for backward compatibility but new code should prefer the generic form) | `Quantum/NeelState.lean` |
| `marshallSignChainConfig_eq_marshallSignOf` / `_square_` / `_cubic_` | the chain / 2D / 3D parity-coloured Marshall signs are precisely `marshallSignOf` instantiated at the corresponding parity colouring | `Quantum/NeelState.lean` |
| `marshallSignSquareConfig` / `marshallSignSquareConfig_neelSquareConfig` | 2D analogue: Marshall sign `∏_{(i,j) with i+j even} (-1)^(σ (i,j))` on `Fin (2K) × Fin (2L)`; equals `+1` on the 2D checkerboard Néel configuration | `Quantum/NeelState.lean` |
| `marshallSignCubicConfig` / `marshallSignCubicConfig_neelCubicConfig` | 3D analogue: Marshall sign `∏_{((i,j),k) with i+j+k even} (-1)^(σ ((i,j),k))` on `(Fin (2K) × Fin (2L)) × Fin (2M)`; equals `+1` on the 3D cubic checkerboard Néel configuration | `Quantum/NeelState.lean` |
| `marshallSignChainConfig_const_zero` / `_const_one` | Marshall sign on the all-up / all-down chain configurations: `marshallSignChainConfig K (const 0) = 1` and `marshallSignChainConfig K (const 1) = (-1)^K` | `Quantum/NeelState.lean` |
| `marshallSignSquareConfig_const_zero` / `_const_one` | 2D Marshall sign on the all-up / all-down checkerboard: both equal `+1` (the all-down case has `2KL` down spins on `A`, so `(-1)^(2KL) = 1`) | `Quantum/NeelState.lean` |
| `marshallSignCubicConfig_const_zero` / `_const_one` | 3D Marshall sign on the all-up / all-down cubic: both equal `+1` (the all-down case has `4KLM` down spins on `A`, so `(-1)^(4KLM) = 1`) | `Quantum/NeelState.lean` |
| `marshallSignChainConfig_flipConfig` | Marshall sign under the global spin-flip on the chain: `marshallSignChainConfig K (flipConfig σ) = (-1)^K · marshallSignChainConfig K σ`. Each of the K even-indexed sites contributes `-1`. Proof: `Finset.prod_mul_distrib` + helper `prod_alternating_neg_one` collapses the contributing factor product to `(-1)^K`, with the per-site identity `(-1)^((1-s).val) = (-1)·(-1)^(s.val)` closed by `fin_cases` | `Quantum/NeelState.lean` |
| `marshallSignSquareConfig_flipConfig` / `marshallSignCubicConfig_flipConfig` | 2D / 3D Marshall sign invariant under the global spin-flip (the contributing factor product `(-1)^(2KL)` resp. `(-1)^(4KLM)` equals `+1` for all K, L, M) | `Quantum/NeelState.lean` |
| `marshallChainState` / `_neelChainConfig` | Marshall-rotated chain basis state `marshallSignChainConfig K σ • basisVec σ`; specialisation at the Néel configuration coincides with `neelChainState K` (since the Marshall sign of the Néel state is `+1`) | `Quantum/NeelState.lean` |
| `marshallSquareState` / `_neelSquareConfig` | 2D Marshall-rotated checkerboard state; coincides with `neelSquareState K L` at the Néel configuration | `Quantum/NeelState.lean` |
| `marshallCubicState` / `_neelCubicConfig` | 3D cubic Marshall-rotated checkerboard state; coincides with `neelCubicState K L M` at the Néel configuration | `Quantum/NeelState.lean` |
| `marshallSignChainConfig_flipConfig_neelChainConfig` / `_square_` / `_cubic_` | Marshall sign on the *flipped* Néel configuration: `(-1)^K` (1D), `+1` (2D), `+1` (3D) — direct compositions of `_flipConfig` and `_neelChainConfig` | `Quantum/NeelState.lean` |
| `marshallChainState_flipConfig_eq_timeReversalSpinHalfMulti` / `_square_` / `_cubic_` | the Marshall-rotated *flipped* Néel state coincides with the time-reversed Néel state in 1D, 2D, 3D — both sides equal the same explicit `(-1)^K` (1D) or `+1` (2D, 3D) scaled basis vector. Establishes a direct bridge between the Marshall basis change (Tasaki §2.5 / Marshall-Lieb-Mattis) and the time-reversal operator (Tasaki §2.3) on the Néel ground-state ansatz | `Quantum/NeelState.lean` |
| `marshallDressedBasis A σ` | **Marshall-dressed standard basis state** `:= marshallSignOf A σ • basisVec σ` on a generic finite vertex type `V` with sublattice indicator `A : V → Bool` (Tasaki §2.5 eq. (2.5.8), p. 41). The dressing produces a basis in which the spin-1/2 antiferromagnetic Heisenberg Hamiltonian on a connected bipartite graph has all off-diagonal matrix elements `≤ 0` (Marshall sign trick), the input to the Perron–Frobenius proof of the MLM theorem | `Quantum/MarshallDressedBasis.lean` |
| `marshallDressedBasis_self` / `_of_ne` / `_apply` | pointwise rules: `Ψ̃^σ σ = marshallSignOf A σ`; `Ψ̃^σ τ = 0` for `τ ≠ σ`; explicit `Ψ̃^σ τ = marshallSignOf A σ · basisVec σ τ` | `Quantum/MarshallDressedBasis.lean` |
| `marshallSignOf_sq_eq_one` | each factor of `marshallSignOf` is `±1`, so the sign squares to `1`: `(marshallSignOf A σ)² = 1` | `Quantum/MarshallDressedBasis.lean` |
| `marshallDressedBasis_inner` | orthonormality of the Marshall-dressed basis under the real bilinear pairing: `Σ_τ Ψ̃^σ τ · Ψ̃^ρ τ = if ρ = σ then 1 else 0` (combines `basisVec_inner` with `marshallSignOf_sq_eq_one`) | `Quantum/MarshallDressedBasis.lean` |
| `marshallDressedBasis_mem_magnetizationSubspace` / `_zero` | the dressed basis state lies in the same magnetisation-`M` subspace `H_M = H_{σ̄/2}` as the underlying `basisVec σ` (Tasaki eq. (2.2.10)); the `_zero` specialisation places it in `H_0` when `Σ_x σ_x = 0` | `Quantum/MarshallDressedBasis.lean` |
| `spinHalfDot_apply_im_eq_zero` | every matrix entry of the two-site spin product `Ŝ_x · Ŝ_y` is **real**: `((spinHalfDot x y) σ σ').im = 0` for all `x, y, σ, σ'`. Case analysis on `x = y` / parallel / antiparallel via the existing `spinHalfDot_mulVec_basisVec_{parallel,antiparallel}` action lemmas. **Property (i) ingredient** for the Marshall–Lieb–Mattis theorem (Tasaki §2.5, p. 41) | `Quantum/MarshallLiebMattis/Realness.lean` |
| `heisenbergHamiltonian_apply_im_eq_zero` | for **real** coupling `J : Λ → Λ → ℂ` (`(J x y).im = 0` for all `x, y`), every matrix entry of the Heisenberg Hamiltonian `H = Σ_{x,y} J(x,y) · spinHalfDot x y` is real: `((heisenbergHamiltonian J) σ σ').im = 0`. ℝ-linearity + `spinHalfDot_apply_im_eq_zero` | `Quantum/MarshallLiebMattis/Realness.lean` |
| `marshallSignOf_im_eq_zero` | the Marshall sign `marshallSignOf A σ` is **real**: `(marshallSignOf A σ).im = 0`. Each factor of the product is `±1 ∈ ℝ` (either `1` or `(-1 : ℂ)^(σ x : ℕ)` with `(σ x : ℕ) ∈ {0, 1}`); products of reals are real | `Quantum/MarshallLiebMattis/Realness.lean` |
| `dot_marshallDressed_heisenbergHamiltonian_marshallDressed_im_eq_zero` | **MLM Property (i)**: for real coupling `J`, the dressed Heisenberg bilinear pairing `Σ_τ \|Ψ̃^σ⟩ τ · (H · \|Ψ̃^{σ'}⟩) τ` is real (Tasaki §2.5, p. 41 in the proof of Theorem 2.2). Reduces to `marshallSignOf A σ · marshallSignOf A σ' · H σ σ'` (each factor real) | `Quantum/MarshallLiebMattis/Realness.lean` |
| `dot_marshallDressed_mulVec_marshallDressed_eq` | for any operator `M`, the dressed bilinear pairing factorises: `Σ_τ \|Ψ̃^σ⟩ τ · (M · \|Ψ̃^{σ'}⟩) τ = marshallSignOf A σ · marshallSignOf A σ' · M σ σ'`. Generalises the inner-product computation used in Property (i) | `Quantum/MarshallLiebMattis/MarshallSignTrick.lean` |
| `marshallSignOf_mul_marshallSignOf_basisSwap_of_bipartite_antiparallel` | **Marshall sign relation**: for a bond `{x, y}` crossing the bipartition (`A x ≠ A y`) with `σ` antiparallel at `{x, y}` (`σ x ≠ σ y`), `marshallSignOf A σ * marshallSignOf A (basisSwap σ x y) = -1`. The combined product over `Λ` of pairwise factors collapses: outside `{x, y}` each pairwise factor is `(±1)² = 1`; at the unique site in `A ∩ {x, y}` the pair contributes `(-1)^(σ x + σ y) = -1` since `σ x ≠ σ y`; the other site of `{x, y}` lies outside `A` and contributes `1` | `Quantum/MarshallLiebMattis/MarshallSignTrick.lean` |
| `bond_dressed_contribution_re_nonpos` | per-bond non-positivity: for `σ ≠ σ'` and any bond `(x, y)` with real non-negative `J(x, y)` supported on bipartite bonds, the contribution `marshallSignOf A σ · marshallSignOf A σ' · J(x,y) · (spinHalfDot x y) σ σ'` to the dressed off-diagonal element has non-positive real part. Case analysis on `(spinHalfDot x y) σ σ'` (zero off-diagonal except at `σ = basisSwap σ' x y`, antiparallel σ', `x ≠ y`) combined with the Marshall sign relation | `Quantum/MarshallLiebMattis/MarshallSignTrick.lean` |
| `dot_marshallDressed_heisenbergHamiltonian_marshallDressed_re_nonpos_of_ne` | **MLM Property (ii)** (Tasaki §2.5, p. 41): for real non-negative `J` supported on bipartite bonds and `σ ≠ σ'`, the dressed off-diagonal Heisenberg pairing `Σ_τ \|Ψ̃^σ⟩ τ · (H · \|Ψ̃^{σ'}⟩) τ` has non-positive real part. Sum bond-by-bond using `bond_dressed_contribution_re_nonpos`. The **Marshall sign trick** at the heart of the Marshall–Lieb–Mattis Theorem 2.2 proof | `Quantum/MarshallLiebMattis/MarshallSignTrick.lean` |
| `SwapStep`, `SwapReachable` | one-step swap relation `σ ↦ basisSwap σ x y` along a graph edge `(x, y)` with `σ x ≠ σ y`; reflexive transitive closure for multi-step reachability | `Quantum/MarshallLiebMattis/Connectivity.lean` |
| `swapReachable_of_walk_of_ne` | for any `G`-walk from `x` to `y` and `σ x ≠ σ y`, `SwapReachable G σ (basisSwap σ x y)`. Walk induction with case analysis on `σ z` at intermediate vertex (Tasaki p. 41 "Proof of Property (iii)" Lemma) | `Quantum/MarshallLiebMattis/Connectivity.lean` |
| `swapReachable_of_reachable_of_ne` / `_preconnected_` | for any `x, y` reachable in `G` (or any `x, y` if `G` preconnected) with `σ x ≠ σ y`, the swap is reachable. **MLM Property (iii) ingredient** (Tasaki §2.5 p. 41) — combined with iteration over the magnetisation-difference, gives Perron–Frobenius irreducibility on `H_M` | `Quantum/MarshallLiebMattis/Connectivity.lean` |
| `H₀Index Λ` | index type `{σ : Λ → Fin 2 // magnetization Λ σ = 0}` for the zero-magnetisation subspace `H_0`; `Fintype` and `DecidableEq` instances | `Quantum/MarshallLiebMattis/H0Matrix.lean` |
| `dressedHeisenbergMatrixH0` | real-valued matrix on `H₀Index Λ` with entries `Re (marshallSignOf A σ · marshallSignOf A τ · (H_J)_{σ,τ})` — the matrix to which Tasaki's Perron–Frobenius proof of MLM applies | `Quantum/MarshallLiebMattis/H0Matrix.lean` |
| `dressedHeisenbergMatrixH0_isSymm` | the matrix is **symmetric** for real symmetric `J` (Hermiticity of Heisenberg + realness of entries) | `Quantum/MarshallLiebMattis/H0Matrix.lean` |
| `dressedHeisenbergMatrixH0_offdiag_nonpos` | **off-diagonal entries are non-positive** for real non-negative bipartite `J` and distinct `σ ≠ τ`, packaged from PR α-3's Property (ii) via `dot_marshallDressed_mulVec_marshallDressed_eq` | `Quantum/MarshallLiebMattis/H0Matrix.lean` |
| `magnetization_basisSwap` | `basisSwap σ x y` preserves total magnetisation. Proof uses the identification `basisSwap σ x y = σ ∘ Equiv.swap x y` (the swap is a permutation of `Λ`); the magnetisation `∑_z spinSign(σ z)` is invariant under such reindexing (`Equiv.sum_comp`). Key ingredient for Tasaki §2.5 p. 42 Proposition (equal-magnetisation reachability) | `Quantum/MarshallLiebMattis/EqMagnetization.lean` |
| `disagreementSet` / `configDist` | the set / count of sites where `σ` and `σ'` disagree; `configDist_eq_zero_iff` characterises configuration equality | `Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean` |
| `exists_swap_pair_of_eq_magnetization` | for `σ ≠ σ'` with equal magnetisation, there exist sites `x` (with `σ x = 0, σ' x = 1`) and `y` (with `σ y = 1, σ' y = 0`). Pigeonhole/cardinality argument: the `(0, 1)`-disagreement and `(1, 0)`-disagreement sets have equal cardinality from magnetisation equality, and the disagreement set is non-empty for `σ ≠ σ'` | `Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean` |
| `configDist_basisSwap_lt` | swapping at sites `x ∈ D01`, `y ∈ D10` strictly decreases the configuration distance to `σ'`. The disagreement set strictly shrinks (`x` newly agrees with `σ'` after swap) | `Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean` |
| `swapReachable_of_eq_magnetization` | **Tasaki §2.5 p. 42 Proposition**: any two configurations `σ`, `σ'` with the same total magnetisation are connected by a chain of single-edge bond swaps, on a connected graph. Strong induction on `configDist`, reducing by `≥ 2` per step via the swap pair from `exists_swap_pair_of_eq_magnetization`. **Final ingredient** for Perron–Frobenius irreducibility on `H_M` | `Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean` |
| `dressedHeisenbergShifted` | the shifted matrix `B := c·I − M` on `H₀Index Λ`. Used as input to Perron–Frobenius: `B` is symmetric, has non-negative off-diagonal (sign flip of `M`'s non-positive off-diagonal), and non-negative diagonal when `c ≥ M σ σ` for all `σ`. The maximum eigenvalue of `B` corresponds to the minimum eigenvalue of `M` (the H_0 ground state of the AFM Heisenberg) | `Quantum/MarshallLiebMattis/H0Shifted.lean` |
| `dressedHeisenbergShifted_isSymm` / `_nonneg` (`_offdiag_nonneg`, `_diag_nonneg`) | symmetry and (off-diagonal / full) non-negativity of `B` under the appropriate hypotheses on `J` and `c` | `Quantum/MarshallLiebMattis/H0Shifted.lean` |
| `spinHalfDot_apply_basisSwap` | the off-diagonal matrix entry `(spinHalfDot x y) σ (basisSwap σ x y) = 1/2` for `x ≠ y` and antiparallel `σ_x ≠ σ_y`. Building block for the explicit Heisenberg matrix entry on swap-related configurations needed for Perron–Frobenius irreducibility | `Quantum/MarshallLiebMattis/SpinDotSwapEntry.lean` |
| `basisSwap_basisSwap_ne_self_of_ne_bond` | combinatorial helper: for `x ≠ y`, `σ_x ≠ σ_y`, and `(u, v) ∉ {(x, y), (y, x)}`, the configuration `basisSwap (basisSwap σ x y) u v ≠ σ`. Site analysis: `σ` and `σ' = basisSwap σ x y` differ at exactly `{x, y}`, so for the iterated swap to return to `σ`, the swap sites `{u, v}` must coincide with `{x, y}`. Used for off-bond vanishing in the Heisenberg matrix entry computation | `Quantum/MarshallLiebMattis/HeisenbergSwapEntry.lean` |
| `spinHalfDot_apply_basisSwap_off_bond_eq_zero` | for `σ' = basisSwap σ x y` (with `x ≠ y`, `σ_x ≠ σ_y`) and any `(u, v) ∉ {(x, y), (y, x)}`, the matrix entry `(spinHalfDot u v) σ σ' = 0`. Three cases: `u = v` (diagonal), `u ≠ v` parallel σ' (constant action), `u ≠ v` antiparallel + off-bond (combinatorial helper) | `Quantum/MarshallLiebMattis/SpinDotOffBond.lean` |
| `heisenbergHamiltonian_apply_basisSwap` | the Heisenberg matrix entry on swap-related configurations: `(heisenbergHamiltonian J) σ (basisSwap σ x y) = (J x y + J y x) / 2`. Decomposes the double sum and uses α-5e (active bond = 1/2) + α-5g (off-bond = 0). For symmetric `J`, simplifies to `J x y` | `Quantum/MarshallLiebMattis/HeisenbergSwapValue.lean` |
| `dressed_pairing_basisSwap_eq` / `dressedHeisenbergMatrixH0_apply_basisSwap` | the dressed Heisenberg matrix entry on swap-related H_0 configurations: complex-level value `-J(x, y)` (Marshall sign trick × Heisenberg formula × symmetric `J`), real-part value `-(J x y).re`. Combined with `J(x, y).re > 0` on graph edges gives strict negativity of M off-diagonal at swap pairs, hence strict positivity of `B = c·I − M` — the input for Perron–Frobenius irreducibility | `Quantum/MarshallLiebMattis/DressedSwapValue.lean` |
| `dressedHeisenbergShifted_pos_of_basisSwap` | strict positivity `0 < B σ τ` on swap-related H_0 configurations with positive symmetric bipartite `J`. Combines the dressed matrix value `-J(x, y).re` (PR α-5i) with the off-diagonal definition `B σ τ = -M σ τ` (PR α-5d). Single-step strict positivity for Perron–Frobenius irreducibility | `Quantum/MarshallLiebMattis/H0ShiftedSwap.lean` |
| `matrix_pow_succ_pos_of_path` | generic matrix-power positivity from a positive path: for non-negative matrix `B` and a path `p_0, ..., p_{k+1}` with `B(p_i, p_{i+1}) > 0` on every consecutive pair, `(B^(k+1))(p_0)(p_{k+1}) > 0`. Induction on `k` using `pow_succ` + `Finset.sum_pos'`. Used to lift single-step swap positivity (α-5j) to multi-step matrix-power positivity for PF irreducibility | `Quantum/MarshallLiebMattis/MatrixPowPath.lean` |
| `matrix_pow_succ_pos_of_pow_pos_step` | one-step extension: if `(B^m) σ τ > 0` and `B τ ρ > 0` for non-negative `B`, then `(B^(m+1)) σ ρ > 0`. Inductive building block for ReflTransGen-style matrix-power lifting | `Quantum/MarshallLiebMattis/MatrixPowExtend.lean` |
| `dressedHeisenbergShifted_pow_pos_of_swapReachable` | for `σ : H₀Index Λ` and any `ξ` with `Relation.ReflTransGen (SwapStep G) σ.val ξ`, there exists `m` with `(B^m) σ ⟨ξ, h_mag⟩ > 0`. Induction on `ReflTransGen`: refl gives `m = 0`, tail extends by one swap using α-5j (single-step swap positivity) and α-5l (one-step matrix-power extension). Key bridge from combinatorial reachability to PF irreducibility | `Quantum/MarshallLiebMattis/H0ShiftedReachable.lean` |
| `dressedHeisenbergShifted_isIrreducible` | **`B = c · I − M` is irreducible** on `H_0` for connected bipartite `G` with positive symmetric real coupling supported on `G`-edges and shift constant `c > M σ σ` (strict). Cases on `σ = τ` (use diagonal positivity) vs `σ ≠ τ` (use α-5c reachability + α-5m matrix-power lift). Final input for Perron–Frobenius application | `Quantum/MarshallLiebMattis/H0ShiftedIrreducible.lean` |
| `dressedHeisenbergShifted_isHermitian` | the shifted matrix is Hermitian (= symmetric for real matrices). Wraps `dressedHeisenbergShifted_isSymm` (PR α-5d) into the IsHermitian form needed by Perron–Frobenius | `Quantum/MarshallLiebMattis/H0PFApplication.lean` |
| `dressedHeisenbergShifted_exists_pos_eigenvec_max` / `_pos_eigenvec_unique` | **Perron–Frobenius applied to `B = c · I − M` on `H_0`**: existence of a strictly positive eigenvector `v` for some real eigenvalue `μ`, and uniqueness up to positive scalar. Translating back to `M`, `v` is the eigenvector for the **minimum** eigenvalue (the H_0 ground state of the AFM Heisenberg). This is the matrix-level Tasaki (2.5.4): the H_0 ground-state expansion `Σ_σ c_σ \|Ψ̃^σ⟩` with `c_σ = v σ > 0` is unique up to positive scalar | `Quantum/MarshallLiebMattis/H0PFApplication.lean` |
| `bipartiteCoupling` / `heisenbergToyHamiltonian` | the Tasaki §2.5 p. 40 toy Hamiltonian setup: `bipartiteCoupling A x y := if A x ≠ A y then 1 else 0` (the unnormalised bipartite coupling), and `heisenbergToyHamiltonian A := heisenbergHamiltonian (bipartiteCoupling A)`. Real symmetric, non-negative, supported on bipartite bonds, positive on inter-sublattice pairs. Hermitian. Used in subsequent PRs to derive `S_tot = 0` for the AFM Heisenberg ground state via inner-product comparison | `Quantum/MarshallLiebMattis/ToyHamiltonian.lean` |
| `bipartiteGraphFromA` | the complete bipartite graph on `Λ` from sublattice indicator `A : Λ → Bool`: vertices `x, y` are adjacent iff `A x ≠ A y`. The natural bond graph for the toy Hamiltonian (every edge of `bipartiteCoupling A` is a `bipartiteGraphFromA A`-edge and vice versa) | `Quantum/MarshallLiebMattis/BipartiteGraph.lean` |
| `bipartiteGraphFromA_preconnected` | `bipartiteGraphFromA A` is preconnected when both sublattices are non-empty. Cases on `A x = A y` (length-2 path via opposite sublattice) vs `A x ≠ A y` (direct edge). Provides the `G.Preconnected` hypothesis needed for MLM application to the toy Hamiltonian | `Quantum/MarshallLiebMattis/BipartiteGraph.lean` |
| `dressedHeisenbergShifted_toy_exists_pos_eigenvec_max` / `_pos_eigenvec_unique` | **Matrix-level Tasaki (2.5.4) for the toy Hamiltonian**: the shifted toy matrix `B_toy = c · I − M_toy` (under both-sublattices-nonempty + diagonal-shift hypothesis) has a unique-up-to-positive-scalar strictly positive eigenvector. Specialises α-5o to the toy via α-6a + α-6b | `Quantum/MarshallLiebMattis/ToyPF.lean` |
| `sublatticeSpinHalfOp1/2/3` | sublattice spin operators `Ŝ_A^(α) := Σ_{x ∈ A} onSite x Ŝ^(α)` for `α ∈ {1, 2, 3}`. Foundation for the Casimir identity `Ĥ_toy = (1/(2|Λ|))((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)` (Tasaki §2.5 (2.5.11)) | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `totalSpinHalfOp{1,2,3}_eq_sublattice_sum` | total spin decomposition: `Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_¬A^(α)` for `α ∈ {1, 2, 3}`. Direct from the partition `Λ = A ∪ ¬A` | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinHalfSquared` / `sublatticeSpinHalfSquared_isHermitian` | sublattice spin Casimir: `(Ŝ_A)² := Σ_α (Ŝ_A^(α))²`. Hermitian (each `(Ŝ_A^(α))²` is the square of a Hermitian operator). Foundation for the Casimir identity `Ĥ_toy = (1/(2|Λ|))((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)` (Tasaki §2.5 (2.5.11)) | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinHalfOpGeneric_cross_commute` / `sublatticeSpinHalfOp{1,2,3}_cross_commute_op{1,2,3}` | mixed-axes cross-sublattice commutativity: `Commute (Ŝ_A^(α)) (Ŝ_¬A^(β))` for any axes `α, β ∈ {1, 2, 3}`. Generic helper expresses this for arbitrary single-site operators `S, T`; the six mixed-axis specialisations follow as one-line corollaries | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinHalfSquared_cross_commute` | the two sublattice Casimirs commute: `Commute (Ŝ_A)² (Ŝ_¬A)²`. Each pairwise component `Commute ((Ŝ_A^(α))²) ((Ŝ_¬A^(β))²)` follows from the mixed-axes cross-commute by chaining `Commute.mul_left` / `mul_right`. Sets up the joint eigenbasis of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` for the toy-Hamiltonian eigenvalue analysis | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinHalfOp{1,2,3}_commutator_sublatticeSpinHalfOp{2,3,1}` | **Sublattice SU(2) algebra**: `[Ŝ_A^(α), Ŝ_A^(β)] = i ε^αβγ Ŝ_A^(γ)` for each cyclic axis triple. Generic helper `sublatticeSpin_commutator_general` lifts the single-site commutator `[Sα, Sβ] = i • Sγ` to the sublattice sum (off-diagonal pairs vanish by `onSite_mul_onSite_of_ne`; diagonal contributes `if A x then i • onSite x Sγ else 0`) | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp{1,2,3}` | **Sublattice Casimir self-invariance**: `Commute (Ŝ_A)² (Ŝ_A^(α))` for each axis. Standard SU(2) Casimir argument applied at the sublattice level: per-axis Leibniz rule `[X², C] = X[X,C] + [X,C]X` combined with the sublattice SU(2) algebra. Together with cross-commute, gives `Commute (Ŝ_A)² (Ŝ_tot^(α))`, hence `Commute (Ŝ_A)² (Ŝ_tot)²` | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinHalfSquared_commute_sublatticeSpinHalfOp{1,2,3}_complement` / `_totalSpinHalfOp{1,2,3}` / `_totalSpinHalfSquared` | `(Ŝ_A)²` commutes with each `Ŝ_¬A^(α)` (`Commute.mul_left` over the mixed-axes cross-commute), with each `Ŝ_tot^(α) = Ŝ_A^(α) + Ŝ_¬A^(α)`, and with `(Ŝ_tot)² = Σ_α (Ŝ_tot^(α))²`. Provides the **third pairwise commutativity** needed for the joint eigenbasis of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` (the first two are α-6r self-invariance and α-6o inter-Casimir cross-commute) | `Quantum/MarshallLiebMattis/SublatticeSpin.lean` |
| `sublatticeSpinDot` / `sublatticeSpinDot_complement_isHermitian` | cross-sublattice spin dot product: `Ŝ_A · Ŝ_B := Σ_α Ŝ_A^(α) Ŝ_B^(α)`. `Ŝ_A · Ŝ_¬A` is Hermitian (each summand is the product of two commuting Hermitian operators). Bilinear expansion `sublatticeSpinDot_eq_sum_sum`: `Ŝ_A · Ŝ_B = Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y` connects the operator-level Casimir form to the bond-level Heisenberg expression in the toy Hamiltonian (Tasaki §2.5 (2.5.10)) | `Quantum/MarshallLiebMattis/SublatticeSpinDot.lean` |
| `sublatticeSpinHalfSquared_eq_sum_dot` / `sublatticeSpinHalfSquared_mulVec_basisVec_const` / `_all_up` / `_all_down` / `_of_const_on` | `(Ŝ_A)² = Σ_{x ∈ A} Σ_{y ∈ A} Ŝ_x · Ŝ_y` (specialisation `B = A` of the bilinear expansion), and the **maximum-spin Casimir eigenvalue on the all-aligned state**: `(Ŝ_A)² · \|s s … s⟩ = (\|A\|·(\|A\|+2)/4) · \|s s … s⟩` for any `s : Fin 2`. Generalised form `_of_const_on`: any `\|σ⟩` with `σ` **constant on `A`** is an eigenvector with eigenvalue `\|A\|·(\|A\|+2)/4` (relevant for Néel-style states which are constant on each sublattice but not globally) | `Quantum/MarshallLiebMattis/SublatticeSpinDot.lean` |
| `heisenbergToyHamiltonian_eq_sublatticeSpinDot_sum` | the MLM toy Hamiltonian decomposes as an oriented cross-sublattice spin dot product: `Ĥ_toy = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A`. Bridges the bipartite-bond sum (Tasaki §2.5 (2.5.10)) to the operator-level Casimir form (Tasaki §2.5 (2.5.11)) | `Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean` |
| `sublatticeSpinDot_complement_comm` / `heisenbergToyHamiltonian_eq_two_sublatticeSpinDot` | cross-sublattice symmetry: `Ŝ_A · Ŝ_¬A = Ŝ_¬A · Ŝ_A` (each axis pair commutes by `sublatticeSpinHalfOp{1,2,3}_cross_commute`), giving the closed form `Ĥ_toy = 2 • Ŝ_A · Ŝ_¬A` | `Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean` |
| `totalSpinHalfSquared_eq_sublattice_casimir` / `heisenbergToyHamiltonian_eq_casimir_diff` | **Casimir identity** (Tasaki §2.5 (2.5.11)): `(Ŝ_tot)² = (Ŝ_A)² + 2 • (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²` (per-axis `(a + b)² = a² + 2ab + b²` via cross-commute), and the closed form (without `1/|Λ|`) `Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²` | `Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean` |
| `heisenbergToyHamiltonian_commute_totalSpinHalfSquared` | the toy Hamiltonian commutes with `(Ŝ_tot)²` (specialisation of `heisenbergHamiltonian_commute_totalSpinHalfSquared`). The standard fact used to project the toy ground state onto a fixed `(Ŝ_tot)²` eigenspace, underpinning the `S_tot = 0` selection of the toy ground state | `Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean` |
| `heisenbergToyHamiltonian_commute_sublatticeSpinHalfSquared` / `_complement` | the toy Hamiltonian commutes with `(Ŝ_A)²` and with `(Ŝ_¬A)²`. Direct consequences of the closed form `Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²` and the three pairwise Casimir commutativities (PRs α-6o, α-6s, self-commute trivially). Together with α-6p, gives all four Casimir-style commutators of `Ĥ_toy`, the prerequisite for the joint eigenbasis analysis on which the `S_tot = 0` selection rests | `Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean` |
| `heisenbergToyHamiltonian_mulVec_basisVec_const` / `_simplified` | explicit eigenvalue of `Ĥ_toy` on the all-aligned state: the Casimir-difference form `\|Λ\|·(\|Λ\|+2)/4 − \|A\|·(\|A\|+2)/4 − \|¬A\|·(\|¬A\|+2)/4` algebraically simplifies via `\|Λ\| = \|A\| + \|¬A\|` to the **product form** `\|A\|·\|¬A\|/2`. The eigenvalue is non-negative for any bipartite lattice and strictly positive when both sublattices are non-empty | `Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean` |
| `sublatticeSpinHalfSquared_mulVec_neelStateOf` / `_complement_mulVec_neelStateOf` | sublattice Casimir eigenvalues on the **Néel state** `Φ_Néel(A) := basisVec (neelConfigOf A)`: `(Ŝ_A)² · \|Φ_Néel(A)⟩ = (\|A\|·(\|A\|+2)/4) · \|Φ_Néel(A)⟩` and `(Ŝ_¬A)² · \|Φ_Néel(A)⟩ = (\|¬A\|·(\|¬A\|+2)/4) · \|Φ_Néel(A)⟩`. Direct corollaries of `_of_const_on` since the Néel configuration is constant on each sublattice (`σ x = 0` on `A`, `σ x = 1` on `¬A`); the Néel state is simultaneously a `(Ŝ_A)²` and `(Ŝ_¬A)²` eigenvector at maximum-spin eigenvalues | `Quantum/MarshallLiebMattis/SublatticeCasimirNeel.lean` |
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
| `spinZDot x y` | the Ising bond operator `σ^z_x · σ^z_y` (generic in `Λ`) | `Quantum/IsingChain.lean` |
| `spinZDot_isHermitian` | each bond operator is Hermitian | `Quantum/IsingChain.lean` |
| `isingHamiltonianGeneric (J : Λ → Λ → ℂ) (h : ℂ)` | **graph-friendly** Ising Hamiltonian `Σ J(x,y) σ^z_x σ^z_y − h Σ σ^x_x` for any finite `Λ` and pairwise coupling `J`; specialises to chain / graph / lattice via the choice of `J` | `Quantum/IsingChain.lean` |
| `isingHamiltonianGeneric_isHermitian` | Hermitian for entry-wise real `J` and real `h` | `Quantum/IsingChain.lean` |
| `isingHamiltonianOnGraph G J h` | graph wrapper: `isingHamiltonianGeneric (couplingOf G J) h`; double-sum convention matches Heisenberg-on-graph | `Quantum/IsingChain.lean` |
| `isingHamiltonianOnGraph_isHermitian` | Hermitian for real `J, h` | `Quantum/IsingChain.lean` |
| `isingGibbsStateOnGraph G β J h` | Gibbs state of the graph-built Ising Hamiltonian | `Quantum/IsingChain.lean` |
| `isingGibbsStateOnGraph_isHermitian` / `isingGibbsStateOnGraph_commute_hamiltonian` | Hermiticity (real `J, h`) and commute with the Hamiltonian | `Quantum/IsingChain.lean` |
| `LatticeSystem.Lattice.sum_pathGraph_forward` / `sum_pathGraph_backward` / `sum_pathGraph_adj` | sum-decomposition helpers for `pathGraph (N+1)` adjacency: `Σ_{x,y}` over ordered adjacent pairs = `Σ_{i:Fin N} (f i.cs i.s + f i.s i.cs)` | `Lattice/Graph.lean` |
| `pathGraphParityColoring` / `pathGraph_isBipartite` | parity-based 2-colouring of `pathGraph (N + 1)` (`i ↦ i.val % 2`) and the corresponding `IsBipartite` proof. Underpins the Néel state (`Quantum/NeelState.lean`) and the Marshall-Lieb-Mattis theorem (Tasaki §2.5) | `Lattice/Graph.lean` |
| `cycleGraphEvenParityColoring` / `cycleGraph_even_isBipartite` | parity-based 2-colouring of the even cycle `cycleGraph (2 * K + 2)` and the corresponding `IsBipartite` proof. Wrap-around case `(2K+1) + 1 ≡ 0` still flips parity because the cycle length is even (odd cycles are not bipartite) | `Lattice/Graph.lean` |
| `quantumIsingHamiltonian_eq_isingHamiltonianGeneric` | **generic-N bridge**: `quantumIsingHamiltonian N J h = isingHamiltonianGeneric (couplingOf (pathGraph (N+1)) (-J/2)) h`. The proof itself is the robust regression test | `Quantum/IsingChain.lean` |

### Testing infrastructure

| Lean name / location | Purpose |
|---|---|
| `LatticeSystem/Tests/Sanity.lean` | sanity-check `example` blocks for concrete small-N instances (Pauli arithmetic, spin-1/2 ladder actions, Heisenberg / Ising Hermiticity on small chains, graph-centric bridge identities) |
| decide-based property tests (in `Tests/Sanity.lean`) | universally-quantified properties verified by `decide` on small finite types (graph adjacency symmetry / irreflexivity / connectivity on `pathGraph n` and `cycleGraph n` for small `n`); real proofs, no `sorry` |
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
| `heisenbergHamiltonianOnGraph G J` | named wrapper = `heisenbergHamiltonian (couplingOf G J)` (parallel to `isingHamiltonianOnGraph`) | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonianOnGraph_isHermitian` / `_commute_totalSpinHalfOp{1,2,3}` / `_commute_totalSpinHalfSquared` | corollaries re-exposed under the named wrapper | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState_eq_onGraph` / `periodicChainHeisenbergGibbsState_eq_onGraph` | rfl bridges: chain Gibbs = graph Gibbs on pathGraph/cycleGraph | `Quantum/HeisenbergChain.lean` |
| `quantumIsingGibbsState_eq_isingGibbsStateOnGraph` | chain Ising Gibbs = `isingGibbsStateOnGraph (pathGraph (N+1)) β (-J/2) h` | `Quantum/IsingChain.lean` |
| `isingCycleGibbsState_commute_hamiltonian` | the periodic Ising Gibbs state commutes with the periodic Ising Hamiltonian (free corollary of `gibbsState_commute_hamiltonian`) | `Quantum/IsingChain.lean` |
| `isingCycleGibbsExpectation_zero` / `_im_of_isHermitian` / `_commutator_hamiltonian` / `_hamiltonian_im` / `_hamiltonian_pow_im` / `isingCycle_partitionFn_im` / `_ofReal_re_eq` / `isingCycleGibbsState_pow_trace` | periodic-Ising expectation companions of the open-chain `quantumIsingGibbsExpectation*` family: β = 0 closed form, real-valuedness for Hermitian observables, conservation `⟨[H, A]⟩ = 0`, energy / energy-power expectations real, partition-function real, real-cast `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`, Rényi-n trace `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` | `Quantum/IsingChain.lean` |
| `hubbardGibbsStateOnGraph N β G J U` | Gibbs state of the graph-built Hubbard Hamiltonian | `Fermion/JordanWigner.lean` |
| `hubbardGibbsStateOnGraph_isHermitian` / `_commute_hamiltonian` | Hermiticity / commute corollaries | `Fermion/JordanWigner.lean` |
| `hubbardChainGibbsState_eq_onGraph` | rfl bridge: `hubbardChainGibbsState = hubbardGibbsStateOnGraph (pathGraph (N+1)) (-J) U` | `Fermion/JordanWigner.lean` |
| `jwStringAbstract i` | Jordan-Wigner string for any `[Fintype Λ] [LinearOrder Λ]` — product of `σ^z_j` over `j < i`; generalises the Fin-specific `jwString` | `Fermion/JWAbstract.lean` |
| `jwStringAbstract_isHermitian` / `jwStringAbstract_sq` / `jwStringAbstract_commute_onSite` | basic structural identities | `Fermion/JWAbstract.lean` |
| `fermionAnnihilationAbstract i` / `fermionCreationAbstract i` / `fermionNumberAbstract i` | abstract-Λ annihilation / creation / number; rfl-bridges to the Fin-specific versions | `Fermion/JWAbstract.lean` |
| `fermionAnnihilationAbstract_conjTranspose` / `fermionCreationAbstract_conjTranspose` / `fermionNumberAbstract_isHermitian` | adjoint relations and Hermiticity in the abstract form | `Fermion/JWAbstract.lean` |
| `fermionAnnihilationAbstract_sq` / `fermionCreationAbstract_sq` | `c_i² = 0`, `c_i†² = 0` (Pauli exclusion) | `Fermion/JWAbstract.lean` |
| `fermionMultiAnticommAbstract_self` / `fermionNumberAbstract_sq` | `{c_i, c_i†} = 1` and `n_i² = n_i` (abstract same-site CAR + idempotency) | `Fermion/JWAbstract.lean` |
| `LatticeSystem.Lattice.boxProd_decidableAdj` | `DecidableRel (G □ H).Adj` for the box product (mathlib provides only the bare definition); enables 2D / nD lattices via `couplingOf` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerChainGraph` | the **infinite** one-dimensional chain `ℤ` as a `SimpleGraph` (= `hasse ℤ`), the infinite-volume analogue of `pathGraph (N+1)` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerChainGraph_adj_iff` | adjacency: `a ~ b ↔ b = a + 1 ∨ a = b + 1` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerSquareLatticeGraph` | the **infinite** 2D square lattice on `ℤ × ℤ` as `integerChainGraph □ integerChainGraph`; infinite analogue of `squareLatticeCoupling` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerSquareLatticeGraph_adj_iff` | adjacency: nearest neighbour in one coordinate, equal in the other | `Lattice/Graph.lean` |
| `squareLatticeCoupling N J`, `squareLatticeHeisenberg_isHermitian` | the 2D open-boundary square lattice on `Fin (N+1) × Fin (N+1)` realised as `couplingOf (pathGraph (N+1) □ pathGraph (N+1)) (-J)`; Hermiticity is a one-line corollary of the graph-generic theorem above | `Quantum/HeisenbergChain.lean` |
| `squareTorusCoupling N J`, `squareTorusHeisenberg_isHermitian` | the 2D periodic square lattice (discrete torus) on `Fin (N+2) × Fin (N+2)` realised as `couplingOf (cycleGraph (N+2) □ cycleGraph (N+2)) (-J)`; Hermiticity is a one-line corollary | `Quantum/HeisenbergChain.lean` |
| `cubicLatticeCoupling N J`, `cubicLatticeHeisenberg_isHermitian` | the 3D open-boundary cubic lattice on `Fin (N+1)^3` realised as `couplingOf (pathGraph (N+1) □ pathGraph (N+1) □ pathGraph (N+1)) (-J)`; Hermiticity is a one-line corollary | `Quantum/HeisenbergChain.lean` |
| `squareLatticeHeisenbergGibbsState` / `_isHermitian` / `_commute_hamiltonian` | Gibbs state of the 2D open-boundary square-lattice Heisenberg Hamiltonian + Hermiticity + commute pair | `Quantum/HeisenbergChain.lean` |
| `squareTorusHeisenbergGibbsState` / `_isHermitian` / `_commute_hamiltonian` | Gibbs state of the 2D torus Heisenberg Hamiltonian + companions | `Quantum/HeisenbergChain.lean` |
| `cubicLatticeHeisenbergGibbsState` / `_isHermitian` / `_commute_hamiltonian` | Gibbs state of the 3D open-boundary cubic-lattice Heisenberg Hamiltonian + companions | `Quantum/HeisenbergChain.lean` |
| `squareLatticeHeisenbergGibbsExpectation_hamiltonian_im` / `squareLatticeHeisenberg_partitionFn_im` | 2D open square-lattice Heisenberg energy expectation real / partition function real | `Quantum/HeisenbergChain.lean` |
| `squareTorusHeisenbergGibbsExpectation_hamiltonian_im` / `squareTorusHeisenberg_partitionFn_im` | 2D torus Heisenberg energy expectation real / partition function real | `Quantum/HeisenbergChain.lean` |
| `cubicLatticeHeisenbergGibbsExpectation_hamiltonian_im` / `cubicLatticeHeisenberg_partitionFn_im` | 3D cubic-lattice Heisenberg energy expectation real / partition function real | `Quantum/HeisenbergChain.lean` |
| `squareLatticeHeisenbergGibbsExpectation_{zero, im_of_isHermitian, commutator_hamiltonian, mul_hamiltonian_im, hamiltonian_sq_im, hamiltonian_pow_im, anticommutator_im, commutator_re, ofReal_re_eq}` / `_GibbsHamiltonianVariance_im` / `_GibbsState_pow_trace` | 2D open square-lattice Heisenberg full Gibbs companion family (PR #334, parity with 1D open / periodic chain). Each is a 1-line application of the generic primitive in `GibbsState*.lean` | `Quantum/HeisenbergLattice.lean` |
| `squareTorusHeisenbergGibbsExpectation_{zero, im_of_isHermitian, commutator_hamiltonian, mul_hamiltonian_im, hamiltonian_sq_im, hamiltonian_pow_im, anticommutator_im, commutator_re, ofReal_re_eq}` / `_GibbsHamiltonianVariance_im` / `_GibbsState_pow_trace` | 2D torus Heisenberg full Gibbs companion family (PR #334) | `Quantum/HeisenbergLattice.lean` |
| `cubicLatticeHeisenbergGibbsExpectation_{zero, im_of_isHermitian, commutator_hamiltonian, mul_hamiltonian_im, hamiltonian_sq_im, hamiltonian_pow_im, anticommutator_im, commutator_re, ofReal_re_eq}` / `_GibbsHamiltonianVariance_im` / `_GibbsState_pow_trace` | 3D cubic-lattice Heisenberg full Gibbs companion family (PR #334) | `Quantum/HeisenbergLattice.lean` |
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

### Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`)

Perron-Frobenius theorem for nonneg irreducible/primitive matrices (Issue #405, closed).
The sorry in `exists_pos_eigenvec_max` is eliminated via the Collatz-Wielandt port (PRs A–C).

| Lean name | Statement | File |
|---|---|---|
| `Matrix.IsPrimitive.of_irreducible_pos_diagonal` | irreducible nonneg + positive diagonal → primitive (Seneta §1.1, Prop. 1.3, p. 17) | `Math/PerronFrobeniusPrimitive.lean` |
| `CollatzWielandt.collatzWielandtFn` | CW function `min_{i\|x_i>0} (Ax)_i/x_i` (Seneta §1.2, p. 27) | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.le_any_ratio` | `CW(x) ≤ (Ax)_i/x_i` for `x_i > 0` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.le_mulVec` | fundamental inequality `CW(x)·x ≤ Ax` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.smul_eq` | scale invariance `CW(cx) = CW(x)` for `c > 0` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.upperSemicontinuousOn` | CW is upper-semicontinuous on stdSimplex | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.exists_maximizer` | CW attains its max on stdSimplex (EVT for USC, Seneta §1.2, p. 28) | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.eq_eigenvalue` | `CW(v) = r` when `Av = r·v`, `v > 0` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.lt_of_all_ratios_gt` | all ratios `> c` ⟹ `CW(x) > c` | `Math/CollatzWielandt.lean` |
| `PerronFrobeniusMain.pos_of_nonneg_eigenvec` | irreducible nonneg + `Av = μv`, `v ≥ 0`, `v ≠ 0` ⟹ `v > 0` (standard propagation argument) | `Math/PerronFrobeniusMain.lean` |
| `PerronFrobeniusMain.exists_positive_eigenvector_of_primitive` | primitive nonneg ⟹ ∃ `r > 0`, `v > 0` with `Av = rv` (Seneta §1.2, pp. 27–28) | `Math/PerronFrobeniusMain.lean` |
| `PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible` | irreducible nonneg ⟹ ∃ `r > 0`, `v > 0` with `Av = rv` (Seneta §1.2, pp. 27–28) | `Math/PerronFrobeniusMain.lean` |
| `exists_nonneg_eigenvec_max` | (**sorry**, retained for docs) symmetric nonneg max eigenvalue has nonneg eigenvector | `Math/PerronFrobenius.lean` |
| `exists_pos_eigenvec_max` | (**sorry-free**) irreducible nonneg Hermitian ⟹ max eigenvalue has strictly positive eigenvector | `Math/PerronFrobenius.lean` |
| `pos_eigenvec_unique` | strictly positive eigenvector unique up to positive scalar | `Math/PerronFrobenius.lean` |

References: E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.), Springer 2006, §1.2 (pp. 27–28);
or4nge19/MCMC: `MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/`.

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
| `fermionMultiAnnihilation_anticomm_zero_pos` | **general cross-site CAR `{c_0, c_k} = 0`** for every `k : Fin (N+1)` with `0 < k.val` — generalises the `_zero_one` / `_zero_two_general` specialisations. Proof: reduce to the anticommutator `{σ^+_0, jwString N k}`, which vanishes by induction on the string length (base: `{σ^+, σ^z} = 0` at site 0; step: `σ^z_{k-1}` at site `k-1 ≠ 0` commutes past `σ^+_0`). | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_anticomm_zero_pos` | dual `{c_0†, c_k†} = 0` for every `k : Fin (N+1)` with `0 < k.val` (adjoint of the above) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_creation_anticomm_zero_pos` | mixed `{c_0, c_k†} = 0` for every `k : Fin (N+1)` with `0 < k.val` — same inductive argument on the JW string anticommutator (the site-`k` factor is `σ^-_k` instead of `σ^+_k`; JW-string part is unchanged) | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_annihilation_anticomm_zero_pos` | mixed dual `{c_0†, c_k} = 0` for every `k : Fin (N+1)` with `0 < k.val` (adjoint of the above) | `Fermion/JordanWigner.lean` |
| `jwStringExceptAt` / `jwString_eq_onSite_mul_jwStringExceptAt` / `jwStringExceptAt_commute_onSite` | private factorisation helpers for the Jordan-Wigner string at an interior site (#210): for `i.val < j.val`, `jwString N j = onSite i pauliZ * jwStringExceptAt N j i`, and `jwStringExceptAt N j i` commutes with every single-site operator at site `i` | `Fermion/JordanWigner.lean` |
| `jwString_anticomm_onSite_pos_spinHalfOpPlus` | operator-level anticommutator `{σ^+_i, jwString N j} = 0` for every `i j : Fin (N+1)` with `i.val < j.val` — generalises `jwString_anticomm_onSite_zero_spinHalfOpPlus` (i = 0 case) to arbitrary interior `i`; building block for the fully general cross-site CAR `{c_i, c_j} = 0` (#210) | `Fermion/JordanWigner.lean` |
| `jwString_anticomm_onSite_pos_spinHalfOpMinus` | companion `{σ^-_i, jwString N j} = 0` for every `i < j` (via `conjTranspose` of the `σ^+` version) | `Fermion/JordanWigner.lean` |
| `jwString_commute_jwString` | any two Jordan-Wigner strings `jwString N i` and `jwString N j` commute (both are noncommutative products of `σ^z` over distinct sites) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_anticomm_lt` | **fully general cross-site CAR `{c_i, c_j} = 0` for `i < j`** (#210) on `Fin (N + 1)`. Proof: reduce via `jwString_anticomm_onSite_pos_spinHalfOpPlus` to an identity involving `JW_i · JW_j = JW_j · JW_i` (via `jwString_commute_jwString`), which makes the sum collapse | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_anticomm_lt` | dual `{c_i†, c_j†} = 0` for `i < j` (adjoint of the above) | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_creation_anticomm_lt` | mixed `{c_i, c_j†} = 0` for `i < j` — same structure as `_anticomm_lt` but with `σ^-_j` at site `j` | `Fermion/JordanWigner.lean` |
| `fermionMultiCreation_annihilation_anticomm_lt` | mixed dual `{c_i†, c_j} = 0` for `i < j` (adjoint of the above) | `Fermion/JordanWigner.lean` |
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
| `fermionGenericGibbsState N β t V` | Gibbs state `gibbsState β (H_hop + V_int)` for the Hubbard-skeleton Hamiltonian | `Fermion/JordanWigner.lean` |
| `fermionGenericGibbsState_isHermitian` | Hermiticity (when `t` is Hermitian and `V` is real) | `Fermion/JordanWigner.lean` |
| `fermionGenericGibbsState_commute_hamiltonian` | `Commute ρ_β H` (always true for the Gibbs state of any operator with itself) | `Fermion/JordanWigner.lean` |
| `fermionMultiVacuum N` | the JW vacuum on `Fin (N+1)` modes — the all-up many-body basis vector `|↑↑…↑⟩` | `Fermion/JordanWigner.lean` |
| `fermionMultiAnnihilation_mulVec_vacuum` | every annihilation operator kills the vacuum: `(c_i).mulVec (fermionMultiVacuum N) = 0` | `Fermion/JordanWigner.lean` |
| `fermionMultiNumber_mulVec_vacuum` | each `n_i · |vac⟩ = 0` (since `n_i = c_i† c_i` and `c_i |vac⟩ = 0`) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_mulVec_vacuum` | the vacuum is an `N̂`-eigenstate of eigenvalue 0 | `Fermion/JordanWigner.lean` |
| `fermionHopping_mulVec_vacuum` | `H_hop · |vac⟩ = 0` (each `c_i† c_j |vac⟩ = c_i† 0 = 0`) | `Fermion/JordanWigner.lean` |
| `fermionDensityInteraction_mulVec_vacuum` | `V_int · |vac⟩ = 0` (each `n_i n_j |vac⟩ = n_i 0 = 0`) | `Fermion/JordanWigner.lean` |
| `fermionGenericHamiltonian_mulVec_vacuum` | `H · |vac⟩ = 0` for the full Hubbard skeleton (linearity) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_mulVec_singleParticle` | `c_i† |vac⟩` is an `N̂`-eigenstate of eigenvalue 1 (uses `[N̂, c_i†] = c_i†` and `N̂ |vac⟩ = 0`) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_mulVec_twoParticle` | `c_i† c_j† |vac⟩` is an `N̂`-eigenstate of eigenvalue 2 (Leibniz on the commutator gives `[N̂, c_i† c_j†] = 2 c_i† c_j†`) | `Fermion/JordanWigner.lean` |
| `fermionTotalNumber_mulVec_eigenstate_of_commute` | generic charge-eigenstate helper: if `[N̂, X] = α X` and `N̂ v = 0` then `N̂ (X v) = α (X v)`; abstracts the single- and two-particle constructions | `Fermion/JordanWigner.lean` |
| `spinfulIndex N i σ` | bijection `(i, σ : Fin 2) ↦ 2 * i + σ ∈ Fin (2*N+2)`, embedding two-species data into a single-species JW chain | `Fermion/JordanWigner.lean` |
| `fermionUpAnnihilation`, `fermionDownAnnihilation`, `fermionUpCreation`, `fermionDownCreation` | spinful annihilation / creation operators as wrappers around the underlying single-species operators at `2i` (up) and `2i+1` (down) | `Fermion/JordanWigner.lean` |
| `fermionUpNumber`, `fermionDownNumber` | spinful site-occupation numbers `n_{i,↑}`, `n_{i,↓}` | `Fermion/JordanWigner.lean` |
| `hubbardOnSiteInteraction N U` | the on-site Hubbard interaction `H_int = U Σ_i n_{i,↑} · n_{i,↓}` | `Fermion/JordanWigner.lean` |
| `hubbardOnSiteInteraction_commute_fermionTotalNumber` | `[H_int, N̂] = 0` (charge conservation) | `Fermion/JordanWigner.lean` |
| `hubbardOnSiteInteraction_isHermitian` | `H_int` is Hermitian when `U` is real (`star U = U`) | `Fermion/JordanWigner.lean` |
| `hubbardKinetic N t` | the spinful tight-binding kinetic operator `T = Σ_{σ} Σ_{i,j} t_{i,j} c_{i,σ}† c_{j,σ}` | `Fermion/JordanWigner.lean` |
| `hubbardKinetic_commute_fermionTotalNumber` | `[T, N̂] = 0` (charge conservation of the kinetic operator) | `Fermion/JordanWigner.lean` |
| `hubbardKinetic_isHermitian` | `T` is Hermitian when `t` is a Hermitian matrix (`star (t i j) = t j i`) | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonian N t U` | the canonical (single-band) Hubbard Hamiltonian `H = T + U Σ n_{i↑} n_{i↓}` on `Fin (2N+2)` | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonian_commute_fermionTotalNumber` | `[H, N̂] = 0` (charge conservation) | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonian_isHermitian` | `H` is Hermitian when `t` is Hermitian and `U` is real | `Fermion/JordanWigner.lean` |
| `hubbardGibbsState N β t U` | the Hubbard Gibbs state `gibbsState β H_Hubbard` | `Fermion/JordanWigner.lean` |
| `hubbardGibbsState_isHermitian` | Hermiticity (Hermitian `t`, real `U`) | `Fermion/JordanWigner.lean` |
| `hubbardGibbsState_commute_hamiltonian` | `Commute ρ_β H_Hubbard` | `Fermion/JordanWigner.lean` |
| `fermionTotalUpNumber`, `fermionTotalDownNumber` | spinful conserved charges `N_↑ = Σ_i n_{i↑}`, `N_↓ = Σ_i n_{i↓}` | `Fermion/JordanWigner.lean` |
| `fermionTotalSpinZ` | total spin polarisation `S^z_tot = (1/2)(N_↑ − N_↓)` | `Fermion/JordanWigner.lean` |
| `fermionTotalUpNumber_commute_fermionTotalDownNumber` | `[N_↑, N_↓] = 0` | `Fermion/JordanWigner.lean` |
| `fermionTotalUpNumber_commute_fermionTotalNumber` / `fermionTotalDownNumber_commute_fermionTotalNumber` | `[N_↑, N̂] = [N_↓, N̂] = 0` | `Fermion/JordanWigner.lean` |
| `fermionTotalSpinZ_commute_fermionTotalNumber` | `[S^z_tot, N̂] = 0` (spin polarisation commutes with total number) | `Fermion/JordanWigner.lean` |
| `fermionTotalUpNumber_commute_hubbardOnSiteInteraction` / `fermionTotalDownNumber_commute_hubbardOnSiteInteraction` | `[N_↑, H_int] = [N_↓, H_int] = 0` | `Fermion/JordanWigner.lean` |
| `fermionTotalSpinZ_commute_hubbardOnSiteInteraction` | `[S^z_tot, H_int] = 0` (free corollary) | `Fermion/JordanWigner.lean` |
| `fermionUpAnnihilation_mulVec_vacuum` / `fermionDownAnnihilation_mulVec_vacuum` | every spinful annihilation kills the JW vacuum | `Fermion/JordanWigner.lean` |
| `fermionUpNumber_mulVec_vacuum` / `fermionDownNumber_mulVec_vacuum` | each spinful site number kills the vacuum | `Fermion/JordanWigner.lean` |
| `fermionTotalUpNumber_mulVec_vacuum` / `fermionTotalDownNumber_mulVec_vacuum` | `N_↑ · |vac⟩ = N_↓ · |vac⟩ = 0` | `Fermion/JordanWigner.lean` |
| `fermionTotalSpinZ_mulVec_vacuum` | `S^z_tot · |vac⟩ = 0` (the vacuum is unpolarised) | `Fermion/JordanWigner.lean` |
| `hubbardKinetic_mulVec_vacuum` / `hubbardOnSiteInteraction_mulVec_vacuum` / `hubbardHamiltonian_mulVec_vacuum` | each annihilates the vacuum (so `|vac⟩` is a 0-energy / 0-particle eigenstate) | `Fermion/JordanWigner.lean` |
| `spinfulIndex_up_ne_down` | the up-channel position `2 i` is never the down-channel position `2 j + 1` | `Fermion/JordanWigner.lean` |
| `fermionTotalDownNumber_commute_fermionUp{Creation,Annihilation,Number}` and the dual `fermionTotalUpNumber_commute_fermionDown{Creation,Annihilation,Number}` | the spinful number on one species commutes with every operator of the other species (different JW positions) | `Fermion/JordanWigner.lean` |
| `fermionTotalDownNumber_commute_upHopping` / `fermionTotalUpNumber_commute_downHopping` | the spinful same-σ hopping term `c_{iσ}† c_{jσ}` commutes with the opposite-spin total number `N_{σ'≠σ}` (cross-spin half of `[H_kinetic, N_σ] = 0`) | `Fermion/JordanWigner.lean` |

#### Hubbard spin symmetry — full SU(2) invariance (Tasaki §9.3.3)

| Lean name | Statement | File |
|---|---|---|
| `fermionTotalUpNumber_isHermitian` / `fermionTotalDownNumber_isHermitian` | `N_↑` and `N_↓` are Hermitian (sum of Hermitian number operators) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalUpNumber_commutator_fermionUpCreation` | `[N_↑, c†_{i,↑}] = c†_{i,↑}` (up-spin sub-chain analogue of `[N̂, c†_i] = c†_i`) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalDownNumber_commutator_fermionDownCreation` | `[N_↓, c†_{i,↓}] = c†_{i,↓}` | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalUpNumber_commute_upHopping` | `[N_↑, c†_{i,↑} c_{j,↑}] = 0` (same-species hopping preserves spin-up count) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalDownNumber_commute_downHopping` | `[N_↓, c†_{i,↓} c_{j,↓}] = 0` | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalUpNumber_commute_hubbardKinetic` / `fermionTotalDownNumber_commute_hubbardKinetic` | `[N_↑, H_kin] = [N_↓, H_kin] = 0` (each spin species conserved by kinetic term) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalUpNumber_commute_hubbardHamiltonian` | `[N_↑, H] = 0` (Tasaki §9.3.3, eq. (9.3.35)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalDownNumber_commute_hubbardHamiltonian` | `[N_↓, H] = 0` (Tasaki §9.3.3, eq. (9.3.35)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinZ_commute_hubbardHamiltonian` | `[S^z_tot, H] = 0` (Tasaki §9.3.3, p. 333) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinPlus` / `fermionTotalSpinMinus` | `Ŝ^+_tot = Σ_i c†_{i,↑}c_{i,↓}`, `Ŝ^-_tot = (Ŝ^+_tot)†` — SU(2) raising/lowering operators (Tasaki §9.3.3, p. 332) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinPlus_conjTranspose` | `(Ŝ^+_tot)† = Ŝ^-_tot` | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionUpAnnihilation_commutator_fermionTotalSpinPlus` | `[c_{j,↑}, Ŝ^+_tot] = c_{j,↓}` (Tasaki §9.3.3, eq. (9.3.36)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionDownCreation_commutator_fermionTotalSpinPlus` | `[c†_{j,↓}, Ŝ^+_tot] = −c†_{j,↑}` (Tasaki §9.3.3, eq. (9.3.36)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionUpCreation_commute_fermionTotalSpinPlus` / `fermionDownAnnihilation_commute_fermionTotalSpinPlus` | `[c†_{i,↑}, Ŝ^+_tot] = 0` and `[c_{j,↓}, Ŝ^+_tot] = 0` (Tasaki §9.3.3, eq. (9.3.36)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinPlus_commute_hubbardHamiltonian` | `[Ŝ^+_tot, H] = 0` (Tasaki §9.3.3, eq. (9.3.35)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinMinus_commute_hubbardHamiltonian` | `[Ŝ^-_tot, H] = 0` (Tasaki §9.3.3, eq. (9.3.35), proved by adjoint) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |

#### Hubbard all-up-spin state and saturated ferromagnetism (Tasaki §11.1.1)

| Lean name | Statement | File |
|---|---|---|
| `hubbardAllUpState N` | fully spin-polarised basis vector: all spin-up orbitals occupied, spin-down empty (even JW indices = 1, odd = 0) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionUpNumber_mulVec_allUpState` | `n_{i,↑} · |↑…↑⟩ = |↑…↑⟩` — each spin-up number operator acts as identity on the all-up state | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionDownNumber_mulVec_allUpState` | `n_{i,↓} · |↑…↑⟩ = 0` — no spin-down electrons; key to the vanishing of `H_int` | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardOnSiteInteraction_mulVec_allUpState` | `H_int · |↑…↑⟩ = 0` — no double occupancy in the fully-polarised state (Tasaki §11.1.1, p. 373; eq. (10.1.5), p. 344) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardHamiltonian_mulVec_allUpState` | `H · |↑…↑⟩ = H_hop · |↑…↑⟩` — the Hubbard model in the all-up sector reduces to a non-interacting hopping problem | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionDownAnnihilation_mulVec_allUpState` | `c_{i,↓} · |↑…↑⟩ = 0` — spin-down annihilation kills the all-up state (odd JW index unoccupied, so σ⁺ maps it to 0) (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionUpCreation_mulVec_allUpState` | `c†_{i,↑} · |↑…↑⟩ = 0` — spin-up creation kills the all-up state (even JW index already occupied, so σ⁻ maps it to 0) (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardKinetic_mulVec_allUpState` | `H_hop · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩` — hopping eigenvalue: off-diagonal terms vanish by CAR anticommutation, diagonal terms give 1 each (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardHamiltonian_mulVec_allUpState_eigenstate` | `H · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩` — full Hamiltonian eigenstate: combines `H_hop` eigenvalue and `H_int · |↑…↑⟩ = 0` (Tasaki §11.1.1, p. 373; eq. (10.1.5), p. 344) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionTotalSpinSquared` | total-spin Casimir `(Ŝ_tot)² = Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z+1)` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalUpNumber_mulVec_allUpState` | `N_↑ · |↑…↑⟩ = (N+1) • |↑…↑⟩` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalDownNumber_mulVec_allUpState` | `N_↓ · |↑…↑⟩ = 0` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinZ_mulVec_allUpState` | `Ŝ^z_tot · |↑…↑⟩ = ((N+1)/2) • |↑…↑⟩` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinPlus_mulVec_allUpState` | `Ŝ⁺_tot · |↑…↑⟩ = 0` — highest-weight state; no down-spin to raise | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinSquared_mulVec_allUpState` | `(Ŝ_tot)² · |↑…↑⟩ = S_max(S_max+1) • |↑…↑⟩` where `S_max = (N+1)/2` (Tasaki §11.1.1, p. 372) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinSquared_commute_hubbardHamiltonian` | `[(Ŝ_tot)², H] = 0` — Casimir commutes with H (from SU(2) invariance, Tasaki §9.3.3) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `isSaturatedFerromagnet` | **Definition 11.1** — Lean predicate: there exists a ground-state energy `E₀` such that every nonzero `H`-eigenvector with eigenvalue `E₀` is a `(Ŝ_tot)²`-eigenvector with eigenvalue `S_max(S_max+1)` (Tasaki §11.1.1, p. 372) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinZ_commutator_fermionTotalSpinMinus` | `[Ŝ^z_tot, Ŝ^-_tot] = -Ŝ^-_tot` — SU(2) algebra relation; follows from site-wise `[Ŝ_z, c†_{i,↓}c_{i,↑}] = -(c†_{i,↓}c_{i,↑})` (Tasaki §9.3.3, p. 332) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinMinus_mulVec_preserves_hamiltonian_eigenvalue` | if `H·v = E·v` then `H·(Ŝ^-·v) = E·(Ŝ^-·v)` — applying `Ŝ^-` preserves Hamiltonian eigenvalues; follows from `[Ŝ^-, H] = 0` (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinZ_mulVec_spinMinus_step` | if `Ŝ_z·v = m·v` then `Ŝ_z·(Ŝ^-·v) = (m-1)·(Ŝ^-·v)` — applying `Ŝ^-` decrements `Ŝ_z` eigenvalue by 1; follows from `[Ŝ^z, Ŝ^-] = -Ŝ^-` (Tasaki §2.4, eq. (2.4.9); §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |

| `hubbardKineticOnGraph N G J` | spinful Hubbard kinetic operator from a `SimpleGraph G` and edge weight `J` | `Fermion/JordanWigner.lean` |
| `hubbardKineticOnGraph_commute_fermionTotalNumber` / `hubbardKineticOnGraph_isHermitian` | charge conservation always; Hermiticity for real `J` | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonianOnGraph N G J U` | full Hubbard Hamiltonian from a graph + on-site coupling | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonianOnGraph_commute_fermionTotalNumber` / `hubbardHamiltonianOnGraph_isHermitian` | charge conservation; Hermiticity for real `J` and real `U` | `Fermion/JordanWigner.lean` |
| `hubbardChainHamiltonian N J U` | the canonical 1D nearest-neighbour Hubbard chain `−J Σ_{σ,⟨i,j⟩} c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}` (built from `pathGraph (N+1)`) | `Fermion/JordanWigner.lean` |
| `hubbardChainHamiltonian_isHermitian` / `hubbardChainHamiltonian_commute_fermionTotalNumber` | Hermiticity (real `J, U`) and charge conservation | `Fermion/JordanWigner.lean` |
| `hubbardHamiltonianOnGraph_mulVec_vacuum` / `hubbardChainHamiltonian_mulVec_vacuum` | both graph-built Hubbard Hamiltonians annihilate the JW vacuum | `Fermion/JordanWigner.lean` |
| `hubbardChainGibbsState N β J U` | Gibbs state of the 1D Hubbard chain | `Fermion/JordanWigner.lean` |
| `hubbardChainGibbsState_isHermitian` / `hubbardChainGibbsState_commute_hamiltonian` | Hermiticity (real `J, U`) and commute with the Hamiltonian | `Fermion/JordanWigner.lean` |
| `hubbardCycleGibbsState_commute_hamiltonian` | the periodic Hubbard Gibbs state commutes with the periodic Hubbard Hamiltonian (companion of the open-chain version, free corollary of `gibbsState_commute_hamiltonian`) | `Fermion/JordanWigner.lean` |
| `hubbardChainGibbsExpectation_zero` / `_im_of_isHermitian` / `_commutator_hamiltonian` / `_hamiltonian_im` / `_hamiltonian_pow_im` / `hubbardChain_partitionFn_im` / `_ofReal_re_eq` / `hubbardChainGibbsState_pow_trace` | open-chain Hubbard expectation companions (β = 0 closed form, Hermitian-observable real, conservation, energy / energy-power expectations real, partition function real, real-cast, Rényi-n trace) | `Fermion/JordanWigner.lean` |
| `hubbardCycleGibbsExpectation_zero` / `_im_of_isHermitian` / `_commutator_hamiltonian` / `_hamiltonian_im` / `_hamiltonian_pow_im` / `hubbardCycle_partitionFn_im` / `_ofReal_re_eq` / `hubbardCycleGibbsState_pow_trace` | periodic Hubbard chain expectation companions (same family as the open chain) | `Fermion/JordanWigner.lean` |

## Continuum-limit roadmap

The project's long-term goals include the `φ^4` / Ising continuum
limit and lattice-QCD-style formalisations, both of which are defined
as limits `a → 0` of families of finite-spacing lattice systems. A
survey of the gap between the current finite-volume matrix framework
and what the continuum limit actually demands was recorded during
Phase A scoping (consulted codex twice on scope and design choices)
and proposes the four phases below.

**Phase A (current, this PR)**. Add a **thin type-level tag**
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

### TODO — Tasaki §2.5 antiferromagnetic deferred items (issue [#240](https://github.com/phasetr/lattice-system/issues/240))

The antiferromagnetic Heisenberg / Néel state machinery in
Tasaki §2.5 is largely formalised (chain / 2D / 3D Néel states +
per-bond expectations `-1/4` + generic graph-centric `neelStateOf`
+ Marshall sign machinery + time-reversal action; see Roadmap row
P1k above). The following subitems remain deferred (large
mathematical work):

- **Marshall-Lieb-Mattis Theorem 2.2** (uniqueness + sign
  structure of the AFM ground state). Requires a Perron-Frobenius
  argument on the Marshall-rotated basis.
- **Problem 2.5.a** (single-cluster ground-state energy
  `-S(1+zS)` for general spin `S` and coordination `z`).
  Requires general-spin infrastructure (depends on P1d''' above).
- **Problem 2.5.b** (lower bound on `E_GS` via 2.5.a).
- **Problem 2.5.c** (single-site expectation `⟨Ŝ_x⟩ = 0` in the
  AFM ground state).
- **Problem 2.5.d** (two-spin correlation under MLM).

The generic graph-centric `neelStateOf` (Phase 3 PR #331) is the
foundation on which these will be built when general-spin and
Perron-Frobenius infrastructure becomes available.

### TODO — remove remaining 7 per-theorem linter suppressions (issue [#377](https://github.com/phasetr/lattice-system/issues/377))

Phase 4 substantially closed `lake build` warnings (zero warnings
+ zero errors as of 2026-04-23), with the exception of 7
per-theorem `set_option linter.{flexible,unusedTactic,unusedSimpArgs} false in`
blocks (4 in `SpinOne{Basis,Decomp}`, 3 in
`SpinHalfRotation/Conjugation`). All are comment-justified and
listed in the [Deprecation window](deprecations.html#remaining-linter-suppressions)
page. Removal requires interactive `simp?` per sub-case.

## Links

- API documentation (doc-gen4): **currently disabled** — the
  CI job was consistently slow (often >1h). To build the API docs
  locally, run
  `lake build +Mathlib:docs` or consult the
  [doc-gen4 README](https://github.com/leanprover-community/doc-gen4).
  The CI job is commented out in
  `.github/workflows/lean_action_ci.yml` with a note on how to
  re-enable.
- [GitHub repository](https://github.com/phasetr/lattice-system)
- [Mathematical guide (`tex/proof-guide.tex`)](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex)
- [ising-model (upstream project)](https://github.com/phasetr/ising-model)
- [Lean by Example](https://lean-ja.github.io/lean-by-example/)
