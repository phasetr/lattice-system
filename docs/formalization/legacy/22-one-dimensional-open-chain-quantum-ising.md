---
layout: page
title: "Legacy catalogue: One-dimensional open-chain quantum Ising"
permalink: /formalization/legacy/22-one-dimensional-open-chain-quantum-ising/
---

# Legacy catalogue: One-dimensional open-chain quantum Ising

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

<!-- legacy-source:start:1301:1324 -->
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

<!-- legacy-source:end:1301:1324 -->

## Authoritative supplemental implementation record (page-citation correction)

This note is maintained by hand and lies outside the migrated catalogue block above; it is not
subject to the frozen byte-for-byte parity of the block above. The `p. 55` citation in the frozen
block above is a historical snapshot and is intentionally left unchanged. For the record: Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, §3.3 heading appears on p. 55, but the
page breaks mid-paragraph and the numbered Hamiltonian eq. (3.3.1) itself is printed on p. 56
(verified against the rendered PDF).

## Authoritative supplemental implementation record (Problem 3.3.a configuration-basis matrix elements)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5386); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.24)-(S.26) on p. 498, eq. (S.27) and the "all other matrix
elements are vanishing" clause on p. 499), for the model of eq. (3.3.1), p. 56, with open
boundary conditions. These are **matrix elements, not energies**: with `h ≠ 0` the configuration
basis states are not eigenstates of the Hamiltonian, and this arc deliberately does not identify
any of these matrix elements with the true Hamiltonian's spectrum.

| Lean name | Statement | File |
|---|---|---|
| `quantumIsingHamiltonian_mulVec_apply` | pointwise action of `quantumIsingHamiltonian N J h` on an arbitrary vector `v` at a configuration `τ`: splits into a diagonal `σ^z σ^z` signed-bond-sum part and an off-diagonal `σ^x` single-site-flip sum; the identity all matrix elements below are read off from | `Quantum/IsingChainMatrixElements.lean` |
| `quantumIsingHamiltonian_apply_diag` | **diagonal matrix element** (Tasaki eqs. (S.24)-(S.25)): `⟨Φ_τ\|Ĥ\|Φ_τ⟩` is `-J` times the signed bond sum of `τ`, with no transverse-field contribution | `Quantum/IsingChainMatrixElements.lean` |
| `quantumIsingHamiltonian_apply_siteFlip` | **single-site-flip off-diagonal matrix element** (Tasaki eqs. (S.26)-(S.27)): `⟨Φ_{siteFlipAt τ x}\|Ĥ\|Φ_τ⟩ = -h`, independently of `J`, `τ`, and the flipped site `x` | `Quantum/IsingChainMatrixElements.lean` |
| `quantumIsingHamiltonian_apply_eq_zero` | all other matrix elements vanish (Tasaki p. 499, "all other matrix elements are vanishing"): configurations that are neither equal nor a single-site flip of one another are not connected by `Ĥ` | `Quantum/IsingChainMatrixElements.lean` |

## Authoritative supplemental implementation record (Problem 3.3.a low-energy 2L matrix)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5387); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.24)-(S.26) on p. 498, eqs. (S.27)-(S.31) and Fig. A.1 on
p. 499), for the model of eq. (3.3.1), p. 56, with open boundary conditions. The spin-`1/2`
convention `σ̂ = 2Ŝ` is §2.1, eqs. (2.1.7)-(2.1.8), p. 15, so the Hamiltonian is
`quantumIsingHamiltonian N (1/4) (λ/2)` on `L = N + 1` sites.

**The `2L` ring of eq. (S.30) is a ring of basis labels, not of lattice sites.** Tasaki's own
Fig. A.1 (p. 499) draws it as a ring of the `2L` basis states `|Φ↓⟩`, `|Φ_j^↑↓⟩`, `|Φ↑⟩`,
`|Φ_j^↓↑⟩` with a spin configuration attached to each site of the ring. Here the labels have type
`ZMod (2 * (N + 1))` while the lattice sites have type `Fin (N + 1)`; the two are never
identified, the chain stays open, and the periodic `isingCycleHamiltonian` is not used. Eq. (S.30)
is printed for `j = 1, …, 2L - 1` but p. 500 uses it at `j = 0`, so the formalization quantifies
over all labels.

These are **matrix elements, not energies**: `Ĥ` does not preserve the span of the `2L`
configurations, so no entry and no eigenvalue of `lowEnergyMatrix` is identified with the true
Hamiltonian's spectrum. Tasaki notes on p. 59 that the analysis of this problem is not
mathematically rigorous.

Every declaration below is **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound` (`wallSite` and the two book-form lemmas need even less).

| Lean name | Statement | File |
|---|---|---|
| `lowEnergyConfig`, `wallSite` | the `2L` low-energy configurations indexed by a label in `ZMod (2 * (N + 1))` (site `x` is up iff the label lies in the arc `x + 1, …, x + L`), and the fold of the label ring onto the chain that names the domain wall of a label | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_natCast_le`, `lowEnergyConfig_natCast_add` | book form of the two families: labels `0, …, L` give `\|Φ↓⟩`, `\|Φ_j^↑↓⟩`, `\|Φ↑⟩` (site `x` up iff `x < j`) and labels `L, …, 2L` give the mirror family `\|Φ_m^↓↑⟩` (site `x` down iff `x < m`) | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_injective` | the `2L` labels give `2L` pairwise distinct configurations, i.e. the low-energy space has the dimension `2L` named in the problem statement | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_succ_eq_siteFlipAt` | advancing the label by one step is exactly the single-site flip `siteFlipAt` at the domain wall `wallSite`; holds for every `N`, the one-site chain `L = 1` included (no `L ≥ 2` hypothesis) | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_ne_of_not_adjacent` | labels that are neither equal nor ring-adjacent give configurations that are neither equal nor a single-site flip of one another (Tasaki p. 499, "all other matrix elements are vanishing", at configuration level); needs `1 ≤ N`, i.e. `L ≥ 2` | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyMatrix`, `ringPotential`, `tightBindingRing` | the `2L × 2L` array of **matrix elements** `⟨Φ_a\|Ĥ\|Φ_b⟩` in the low-energy configuration basis; the potential `v_j` of eq. (S.30) (`0` at the aligned labels `0` and `L`, `1/2` elsewhere); the tight-binding operator on the labels with hopping `-λ/2` between ring-adjacent labels | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyMatrix_eq_add_tightBindingRing` | **capstone of PR #5387**: every entry at once, `lowEnergyMatrix N λ = (-N/4) • 1 + tightBindingRing N λ` for `1 ≤ N` — Tasaki eqs. (S.24)-(S.27) together with "all other matrix elements are vanishing" (p. 499), subsuming the printed index ranges of (S.25) and (S.26) | `Quantum/IsingLowEnergyProblem33a.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem33aLowEnergy.lean`: the `L = 2` diagonal
entries pin `E_GS^(0) = -(L-1)/4 = -1/4` (a physically periodic chain would give `-1/2`), and the
`L = 3` entry between the labels `0` and `2L - 1 = 5` pins the wrap-around of the label ring.

## Authoritative supplemental implementation record (Problem 3.3.a eigenvalue equation and ansatz)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5388); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.28)-(S.31) on p. 499, eqs. (S.32)-(S.34) on p. 500), for the
model of eq. (3.3.1), p. 56, with open boundary conditions and the spin-`1/2` convention
`σ̂ = 2Ŝ` of §2.1, eqs. (2.1.7)-(2.1.8), p. 15.

This layer turns the compressed matrix of the previous section into explicit eigenvectors. The
expansion (S.28)-(S.29) of a low-energy state in the `2L` basis configurations makes the
eigenvector equation of `lowEnergyMatrix` equivalent to the scalar recursion (S.30); the ansatz
(S.32) solves the recursion at every label carrying a domain wall for any decay rate `κ`, and the
root equation (S.34) is exactly the remaining condition at the two aligned labels `0` and `L`.

The recursion is quantified over **all** labels `j : ZMod (2 * (N + 1))`. Eq. (S.30) is printed
"for any `j = 1, …, 2L - 1`", yet p. 500 derives (S.33) from it at `j = 0` and `j = L`; the
quantified form is the eigenvector equation of the `2L × 2L` matrix and subsumes both readings.

These are **eigenvalues of the compression, not energies**: `Ĥ` does not preserve the span of the
`2L` configurations, so `tightBindingEnergy λ κ` is not identified with a ground-state or
first-excited energy of `Ĥ`, and the source's non-rigorous identifications (S.36)-(S.38) are not
asserted. Tasaki notes on p. 59 that the analysis of this problem is not mathematically rigorous.

Every declaration below is **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `lowEnergyMatrix_mulVec_eq_iff` | Tasaki eqs. (S.28)-(S.30): for `1 ≤ N`, the eigenvector equation `lowEnergyMatrix N λ *ᵥ φ = (E_GS^(0) + ε) • φ` holds exactly when `ε φ_j = -(λ/2)(φ_{j-1} + φ_{j+1}) + v_j φ_j` at every label `j`, with `v_j = ringPotential N j` | `Quantum/IsingLowEnergyProblem33aEigenvectors.lean` |
| `tightBindingEnergy`, `lowEnergyAnsatz`, `rootEquation` | the eigenvalue `ε = -(λ/2)(e^κ + e^-κ) + 1/2` of eq. (S.31); the two-branch ansatz of eq. (S.32), `φ_j = e^-κj + s e^-κ(L-j)` for `j = 0, …, L` and `φ_j = s e^-κ(j-L) + e^-κ(2L-j)` for `j = L, …, 2L`, the sign `s = ±1` selecting the symmetric resp. antisymmetric solution `φ_L = s φ_0`; the root equation of eq. (S.34), `e^κ - e^-κ = λ^-1 (1 + s e^-κL)/(1 - s e^-κL)`, carrying the same sign in numerator and denominator | `Quantum/IsingLowEnergyProblem33aEigenvectors.lean` |
| `lowEnergyAnsatz_ne_zero` | the ansatz is not the zero vector: its value `1 + s e^-κL` at the label `0` is positive for `0 < κ` and either sign | `Quantum/IsingLowEnergyProblem33aEigenvectors.lean` |
| `lowEnergyAnsatz_isEigenvector` | **capstone of PR #5388**: Tasaki eqs. (S.28)-(S.34) assembled — for `1 ≤ N`, `0 < λ`, `0 < κ` and `s = ±1` satisfying the root equation, the ansatz is a nonzero eigenvector of `lowEnergyMatrix N λ` with eigenvalue `E_GS^(0) + tightBindingEnergy λ κ` | `Quantum/IsingLowEnergyProblem33aEigenvectors.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem33aLowEnergy.lean`: the parity fixture
pins `φ_L = s φ_0`, and the numeric fixtures at `L = 2`, `κ = log 2` pin the six values
`5/4, 1, 5/4` (symmetric) and `3/4, 0, -3/4` (antisymmetric) on the labels `0, 1, 2` together
with the second-branch value at the label `3`.

## Authoritative supplemental implementation record (Problem 3.3.a infinite-chain decay rate)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5389); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eq. (S.35) on p. 500, eq. (S.39) on p. 501), for the model of
eq. (3.3.1), p. 56, with open boundary conditions and the spin-`1/2` convention `σ̂ = 2Ŝ` of §2.1,
eqs. (2.1.7)-(2.1.8), p. 15.

Letting `L ↑ ∞` in the root equation (S.34) of the previous section sends its right-hand side to
`λ^-1`, so the two parity sectors share one limiting decay rate `κ∞`, characterised by (S.35) as
`e^κ∞ - e^-κ∞ = λ^-1`. Since the left-hand side is `2 sinh κ∞`, the solution is
`arsinh (1 / (2λ))`, and substituting it into the eigenvalue (S.31) gives the middle equality of
(S.39), `ε∞ = -(λ/2)(e^κ∞ + e^-κ∞) + 1/2 = -√(1 + 4λ²)/2 + 1/2`. The radical `√(1 + 4λ²)` is
present in the rendered source on p. 501.

The trailing `≃ -λ²` of (S.39) is a small-`λ` approximation and is not asserted. The two limits
recorded below are the small-`λ` replacements `e^-κ∞ ≃ λ` (p. 500, below (S.35)) and
`tanh κ∞ ≃ 1` behind the final form `E_1st - E_GS ≃ 2 λ^L` of (S.41).

These remain **eigenvalues of the compression, not energies**: `Ĥ` does not preserve the span of
the `2L` configurations, so `ε∞` is the `L ↑ ∞` value of an eigenvalue of `lowEnergyMatrix` and is
not identified with a ground-state or first-excited energy of `Ĥ`; the source's non-rigorous
Taylor steps (S.36)-(S.38) are not asserted. Tasaki notes on p. 59 that the analysis of this
problem is not mathematically rigorous.

Every declaration below is **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `kappaInf`, `kappaInf_pos` | the `L ↑ ∞` decay rate of Tasaki eq. (S.35), `arsinh (1 / (2λ))`, and its positivity for `0 < λ` | `Quantum/IsingLowEnergyProblem33aSpectrum.lean` |
| `exp_kappaInf_sub_exp_neg` | Tasaki eq. (S.35) itself: `e^κ∞ - e^-κ∞ = λ^-1` for `0 < λ` | `Quantum/IsingLowEnergyProblem33aSpectrum.lean` |
| `exp_neg_kappaInf_eq` | the closed radical form `e^-κ∞ = 2λ / (1 + √(1 + 4λ²))`, the reciprocal of `e^κ∞ = (1 + √(1 + 4λ²)) / (2λ)` | `Quantum/IsingLowEnergyProblem33aSpectrum.lean` |
| `tightBindingEnergy_kappaInf_eq` | **capstone of PR #5389**: the middle equality of Tasaki eq. (S.39), `ε∞ = -(λ/2)(e^κ∞ + e^-κ∞) + 1/2 = (1 - √(1 + 4λ²))/2` for `0 < λ` | `Quantum/IsingLowEnergyProblem33aSpectrum.lean` |
| `tanh_kappaInf_eq` | `tanh κ∞ = 1/√(1 + 4λ²)`, the ratio `(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)` carried by Tasaki eqs. (S.40) and (S.41) | `Quantum/IsingLowEnergyProblem33aSpectrum.lean` |
| `tendsto_exp_neg_kappaInf_div_atZero`, `tendsto_tanh_kappaInf_atZero` | the two small-`λ` replacements behind the final form of Tasaki eq. (S.41): `e^-κ∞ / λ → 1` and `tanh κ∞ → 1` as `λ ↓ 0` | `Quantum/IsingLowEnergyProblem33aSpectrum.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem33aLowEnergy.lean`: the value fixture at
`λ = 1/2` pins `ε∞ = (1 - √2)/2` from the middle equality of (S.39), and the companion fixture
pins the prefactor `2 tanh κ∞ = √2` of (S.41) at the same `λ`.

## Authoritative supplemental implementation record (Problem 3.3.a root existence and ordering)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5390); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.33) and (S.34) on p. 500, eq. (S.40) on p. 501), for the model
of eq. (3.3.1), p. 56, with open boundary conditions and the spin-`1/2` convention `σ̂ = 2Ŝ` of
§2.1, eqs. (2.1.7)-(2.1.8), p. 15.

Substituting the ansatz (S.32) into the recursion (S.30) at the label `j = 0` (equivalently at
`j = L`) gives (S.33), `ε (1 ± e^-κL) = -λ (e^-κ ± e^-κ(L-1))` with the same sign on both sides,
and eliminating `ε` through (S.31) gives the root equation (S.34),
`e^κ - e^-κ = λ^-1 (1 ± e^-κL) / (1 ∓ e^-κL)`, whose numerator and denominator carry *opposite*
signs; the upper signs belong to the symmetric and the lower ones to the antisymmetric solution.

`rootEquation_iff_cleared` removes that denominator, turning (S.34) into
`λ (e^κ - e^-κ) (1 - s e^-κL) = 1 + s e^-κL`. The left factor `λ (e^κ - e^-κ) = 2 λ sinh κ` is
strictly increasing and equals `1` at the `L ↑ ∞` rate `κ∞` of (S.35), so a sign change of the
cleared equation's defect locates a root by the intermediate value theorem. This yields a root in
the symmetric sector at every ring size and one in the antisymmetric sector for all large `L`;
comparing the two sectors gives the exact ordering that the source states after (S.40),
`ε_± ≃ ε∞ ∓ [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L`, namely "We see that the symmetric
solution has a lower energy, as it should be".

Only that ordering is asserted. The displayed `≃` form of (S.40), which the source derives from the
non-rigorous Taylor steps (S.36)-(S.38), is not asserted, and the comparison uses no asymptotics.
Uniqueness of the root in either sector is neither proved nor used: every statement quantifies over
all positive roots. The antisymmetric root is produced only once `L` exceeds a multiple of `λ`, so
its existence is stated for all sufficiently large ring sizes rather than for every one.

These remain **eigenvalues of the compression, not energies**: `Ĥ` does not preserve the span of
the `2L` configurations, so `tightBindingEnergy` is an eigenvalue of `lowEnergyMatrix` and is not
identified with a ground-state or first-excited energy of `Ĥ`. Tasaki notes on p. 59 that the
analysis of this problem is not mathematically rigorous. The ring carrying the labels `j` is a ring
of basis labels of type `ZMod (2 * (N + 1))`, not of lattice sites: the chain itself stays open.

Every declaration below is **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `rootEquation_iff_cleared` | Tasaki eq. (S.34) with its denominator cleared: for `0 < κ` and `s = ±1`, the root equation is equivalent to `λ (e^κ - e^-κ) (1 - s e^-κL) = 1 + s e^-κL` | `Quantum/IsingLowEnergyProblem33aRoots.lean` |
| `exists_root_symmetric` | for every ring size and every `0 < λ`, the symmetric (`s = 1`) root equation (S.34) has a positive solution `κ` | `Quantum/IsingLowEnergyProblem33aRoots.lean` |
| `eventually_exists_root_antisymmetric` | for every `0 < λ` and every sufficiently large ring size, the antisymmetric (`s = -1`) root equation (S.34) has a positive solution `κ` | `Quantum/IsingLowEnergyProblem33aRoots.lean` |
| `tightBindingEnergy_lt_of_roots` | **capstone of PR #5390**: the exact ordering behind Tasaki eq. (S.40), `ε_+ < ε_-`, for any positive root of the symmetric and any positive root of the antisymmetric equation | `Quantum/IsingLowEnergyProblem33aRoots.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem33aLowEnergy.lean`: each of the four
declarations above has a signature fixture restating it in full and discharging it by the
declaration itself.

## Authoritative supplemental implementation record (Problem 3.3.a splitting limit (S.41))

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5391); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.34)-(S.38) and footnote 1 on p. 500, eqs. (S.39)-(S.41) on
p. 501), for the model of eq. (3.3.1), p. 56, with open boundary conditions.

The source fixes the decay rate by writing `κ = κ∞ + δ` and expanding: (S.36),
`e^{κ∞+δ} - e^{-κ∞-δ} ≃ λ^-1 (1 ± 2 e^-κ∞L)`; (S.37),
`δ ≃ ±λ^-1 2 e^-κ∞L/(e^κ∞ + e^-κ∞)`, introduced by "Expanding the left-hand side in `δ` to the
lowest order"; (S.38), `ε ≃ ε∞ - (λ/2)(e^κ∞ - e^-κ∞) δ`. Substituting (S.37) it then states
(S.40), `ε_± ≃ ε∞ ∓ [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L`, and (S.41),
`E_1st - E_GS = ε_- - ε_+ ≃ 2 [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L ≃ 2 λ^L`.

None of those `≃` is asserted. `tendsto_splitting_ratio` asserts the middle expression of (S.41)
as an exact limit: the ratio of the difference of the two sectors' eigenvalues to
`2 tanh κ∞ e^-κ∞L` tends to `1` as the ring size grows, at fixed `λ` — the order of limits of
the source's footnote 1 on p. 500, "we fix small `λ`, and then make `L` large". The prefactor is
`tanh κ∞` because `(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)` is exactly that.

Two exact ingredients replace the source's two non-rigorous moves. The Taylor step
(S.36)-(S.38) is replaced by the identity
`ε(κ_-) - ε(κ_+) = tanh((κ_+ + κ_-)/2) (hop λ κ_+ - hop λ κ_-)/2`, an equality valid at all
arguments, where `hop λ κ = λ (e^κ - e^-κ)` is the left-hand side of (S.34) times `λ`. The
source's "`L ≫ 1`" is replaced by localization of the roots: `root_symmetric_gt_kappaInf` places
every positive symmetric root strictly above `κ∞` at every ring size, and
`eventually_root_antisymmetric_mem_Ico` places every positive antisymmetric root in
`[arsinh (3/(8λ)), κ∞)` for all sufficiently large ring sizes, so that the limit statement is
taken along `∀ᶠ N in atTop`.

Limitations measured in this layer. Uniqueness of the root in either sector is neither proved nor
used: the limit quantifies over arbitrary families of positive roots of the two sectors, one per
ring size. The `∀ᶠ` of the antisymmetric localization is not cosmetic: the lower bound excludes
roots with `e^-κL > 1/8`, which the cleared equation permits only while the ring size stays below
a multiple of `λ e^κ∞`. The final step `≃ 2 λ^L` of (S.41) is not asserted here; its two
small-`λ` replacements, `tendsto_exp_neg_kappaInf_div_atZero` and `tendsto_tanh_kappaInf_atZero`,
are limits in `λ` at no fixed ring size and are not combined with the `L ↑ ∞` limit above.

These remain **eigenvalues of the compression, not energies**: `Ĥ` does not preserve the span of
the `2L` configurations, so `tightBindingEnergy` is an eigenvalue of `lowEnergyMatrix` and the
difference above is not identified with `E_1st - E_GS` of `Ĥ`. Tasaki notes on p. 59 that the
analysis of this problem is not mathematically rigorous. The ring carrying the labels `j` is a
ring of basis labels of type `ZMod (2 * (N + 1))`, not of lattice sites: the chain itself stays
open.

`hop`, `hop_strictMono`, `hop_kappaInf_eq_one` and `hop_continuous` of
`Quantum/IsingLowEnergyProblem33aRoots.lean`, previously `private` to that module, are public in
this PR so that the splitting layer consumes them from their single defining site.

Every declaration below is **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `root_symmetric_gt_kappaInf` | every positive root of the symmetric (`s = 1`) form of (S.34) lies strictly above `κ∞`, at every ring size | `Quantum/IsingLowEnergyProblem33aSplitting.lean` |
| `eventually_root_antisymmetric_mem_Ico` | for all sufficiently large ring sizes, every positive root of the antisymmetric (`s = -1`) form of (S.34) lies in `[arsinh (3/(8λ)), κ∞)` | `Quantum/IsingLowEnergyProblem33aSplitting.lean` |
| `tendsto_splitting_ratio` | **capstone of PR #5391**: for arbitrary families of positive roots of the two sectors, the ratio of the eigenvalue difference to `2 tanh κ∞ (e^-κ∞)^(N+1)` tends to `1`, the middle expression of (S.41) as an exact limit | `Quantum/IsingLowEnergyProblem33aSplitting.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem33aLowEnergy.lean`: each of the three
declarations above has a signature fixture restating it in full and discharging it by the
declaration itself.

---

[← Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))](/lattice-system/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/) · [Catalogue](/lattice-system/formalization/legacy/) · [Testing infrastructure →](/lattice-system/formalization/legacy/23-testing-infrastructure/)
