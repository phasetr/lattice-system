---
layout: page
title: "Roadmap history: P0 through P1j"
permalink: /history/roadmap/foundations/
---

# Roadmap history: P0 through P1j

> Historical implementation record normalized from the former roadmap table. Active work is governed by tracking Issues.

<!-- legacy-source:start:114:114 -->
## P0: Project skeleton, CI, documentation infrastructure

Done
<!-- legacy-source:end:114:114 -->

<!-- legacy-source:start:115:115 -->
## P1a: Finite-volume quantum spin operator algebra (Pauli, `onSite`, commutativity)

Done
<!-- legacy-source:end:115:115 -->

<!-- legacy-source:start:116:116 -->
## P1b: Finite-chain quantum Ising Hamiltonian, Hermiticity, Gibbs state instantiation (Hermiticity, commutativity with `H`, β = 0 closed form, expectation realness for Hermitian observables, conservation `⟨[H, A]⟩ = 0`, energy expectation as bond + transverse-field decomposition, energy expectation real, `⟨H · O⟩` real for Hermitian `O`, `⟨H^n⟩` real for any `n : ℕ`)

Done
<!-- legacy-source:end:116:116 -->

<!-- legacy-source:start:117:117 -->
## P1c (Tasaki §2.1): Spin-1/2 operators `Ŝ^(α)` and the commutator algebra

Done
<!-- legacy-source:end:117:117 -->

<!-- legacy-source:start:118:118 -->
## P1d (Tasaki §2.1): Basis states `|ψ^↑⟩, |ψ^↓⟩`, raising/lowering `Ŝ^±` (S = 1/2)

Done
<!-- legacy-source:end:118:118 -->

<!-- legacy-source:start:119:119 -->
## P1d' (Tasaki §2.1): S = 1 matrix representations (eq. (2.1.9))

Done
<!-- legacy-source:end:119:119 -->

<!-- legacy-source:start:120:120 -->
## P1d'' (Tasaki §2.1): Problem 2.1.a for S = 1/2 (Pauli basis of `M_2(ℂ)`)

Done
<!-- legacy-source:end:120:120 -->

## Authoritative supplemental implementation record (P1d'': Problem 2.1.a for S = 1/2)

This section is maintained by hand, lies outside the migrated blocks on this page, and records the
current implementation of the P1d'' milestone above. That block is a frozen historical record — it
is pinned byte-for-byte by `scripts/check_docs_hierarchy.py` and is never edited for later
relocations or deletions.

The milestone stays Done, and is now carried by P1d''' below: `spinS_adjoin_eq_top`
(`Quantum/SpinS/SpanningTheorem.lean`) proves `Algebra.adjoin ℂ {Ŝ^(1)_N, Ŝ^(2)_N, Ŝ^(3)_N} = ⊤`
for every `N`, so `N := 1` is the `S = 1/2` case, and the bridges
`spinSOp{1,2,3}_one_eq_spinHalfOp{1,2,3}` (`Quantum/SpinS/SpinHalfSpecialization.lean`) restate that
instance in the concrete `spinHalfOp` vocabulary in one line.

The dedicated spin-1/2 module `Quantum/SpinHalfDecomp.lean` that originally discharged this
milestone (`pauliCoeff{0,1,2,3}`, `pauli_decomposition`, `spinHalf_decomposition`,
`pauli_linearIndep`) has therefore been removed in full; no *other* Lean file referenced any of its
names — within the module itself, `spinHalf_decomposition` referenced `pauli_decomposition` and the
three bridges `pauli{X,Y,Z}_eq_two_smul_spinHalfOp{1,2,3}` (`Quantum/SpinHalf.lean`).
Its explicit coefficient formulas and the linear independence of `{1, σ^x, σ^y, σ^z}` were content
beyond Problem 2.1.a, which asks only for polynomial expressibility. Tasaki eq. (2.1.8)
`σ^(α) = 2 Ŝ^(α)` — `pauli{X,Y,Z}_eq_two_smul_spinHalfOp{1,2,3}` in `Quantum/SpinHalf.lean`, whose
only consumer was the retired module — keeps its statements: it is a catalogued row of the
[spin-1/2 operators page](/lattice-system/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/)
and no public generic states it.

<!-- legacy-source:start:121:121 -->
## P1d''' (Tasaki §2.1): Problem 2.1.a for `S ≥ 1` (polynomial basis of `M_{2S+1}(ℂ)` via Lagrange interpolation in `Ŝ^(3)` and `Ŝ^±` ladder action)

**Done for general `S ≥ 1`** — `spinS_adjoin_eq_top` (Issue #458 closed in PR #490). Algebra
spanned: `Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}} = ⊤`.
<!-- legacy-source:end:121:121 -->

<!-- legacy-source:start:122:122 -->
## P1e (Tasaki §2.1): S = 1/2 rotation `Û^(α)_θ` closed form, `Û_0`, adjoint, `Û_{2π}`

Done
<!-- legacy-source:end:122:122 -->

<!-- legacy-source:start:123:123 -->
## P1e': Rotation group law and unitarity

Done
<!-- legacy-source:end:123:123 -->

<!-- legacy-source:start:124:124 -->
## P1e'' (Tasaki §2.1): `Û^(α)_θ = exp(-iθŜ^(α))` via `Matrix.exp_diagonal` + `Matrix.exp_conj` (Problem 2.1.b, all 3 axes)

Done
<!-- legacy-source:end:124:124 -->

<!-- legacy-source:start:125:125 -->
## P1e''' (Tasaki §2.1): π-rotations: `Û^(α)_π = -2i·Ŝ^(α)`, anticommutation at distinct axes

Done
<!-- legacy-source:end:125:125 -->

<!-- legacy-source:start:126:126 -->
## P1e'''' (Tasaki §2.1): `Û^(α)_π · Û^(β)_π = Û^(γ)_π`; conjugations `(Û^(α)_π)†·Ŝ^(β)·Û^(α)_π = ±Ŝ^(β)`

Done
<!-- legacy-source:end:126:126 -->

<!-- legacy-source:start:127:127 -->
## P1e''''' (Tasaki §2.1): General θ transformation `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) - sin θ · ε^{αβγ} Ŝ^(γ)` (eq. (2.1.16))

Done
<!-- legacy-source:end:127:127 -->

<!-- legacy-source:start:128:128 -->
## P1e'''''' (Tasaki §2.1): Z₂ × Z₂ representation (eqs. (2.1.27)-(2.1.34)): S = 1/2 projective + S = 1 genuine

Done
<!-- legacy-source:end:128:128 -->

<!-- legacy-source:start:129:129 -->
## P1d-S1 (Tasaki §2.1): S = 1 basis states and `Ŝ^(3)`, `Ŝ^±` actions (eqs. (2.1.2)–(2.1.6) for S = 1)

Done
<!-- legacy-source:end:129:129 -->

<!-- legacy-source:start:130:130 -->
## P1f (Tasaki §2.2): Abstract lattice `Λ`, site operators `Ŝ_x^(α)`, distinct-site commutation (eq. (2.2.6), `x ≠ y`)

Done
<!-- legacy-source:end:130:130 -->

<!-- legacy-source:start:131:131 -->
## P1f-same (Tasaki §2.2): Same-site commutation `[Ŝ_x^(α), Ŝ_x^(β)] = i·ε^{αβγ} Ŝ_x^(γ)` (eq. (2.2.6), `x = y`)

Done
<!-- legacy-source:end:131:131 -->

## Authoritative supplemental implementation record (P1f-same: same-site commutation)

This section is maintained by hand, lies outside the migrated blocks on this page, and records the
current implementation of the P1f-same milestone above. That block is a frozen historical record —
it is pinned byte-for-byte by `scripts/check_docs_hierarchy.py` and is never edited for later
relocations or deletions.

The milestone itself is unchanged: Tasaki eq. (2.2.6) at `x = y` is realised by the generic
`onSite_commutator_same` (`Quantum/ManyBody.lean`), which lifts any single-site commutator through
the site embedding, applied to the single-site relations
`spinHalfOp{1,2,3}_commutator_spinHalfOp{2,3,1}` (`Quantum/SpinHalf.lean`). The three named
spin-`1/2` specialisations in `Quantum/TotalSpin.lean` —
`spinHalfOp1_onSite_commutator_spinHalfOp2_onSite`,
`spinHalfOp2_onSite_commutator_spinHalfOp3_onSite` and
`spinHalfOp3_onSite_commutator_spinHalfOp1_onSite` — were retired: each was the single `rw` chain
composing those two ingredients with `onSite_smul` (`Quantum/ManyBody.lean`) to restate the
commutator in the `c • onSite x Sγ` form the statement quotes, and no Lean file referenced them.
All three ingredients remain in the library with their own consumers.

The neighbouring milestone P1f (eq. (2.2.6) at `x ≠ y`) is likewise unchanged, and is realised by
`onSite_mul_onSite_of_ne` (`Quantum/ManyBody.lean`), which states the distinct-site commutation for
arbitrary single-site matrices under an explicit `i ≠ j` hypothesis and is consumed across the
library. Its spin-`1/2` wrapper `spinHalfOp_onSite_comm_of_ne` in `Quantum/TotalSpin.lean` was
retired: it applied that theorem verbatim under renamed variables, adding no hypothesis and no
proof step, and no Lean file referenced it.

<!-- legacy-source:start:132:132 -->
## P1f' (Tasaki §2.2): Total spin operator `Ŝ_tot^(α)` (eq. (2.2.7)) and Hermiticity

Done
<!-- legacy-source:end:132:132 -->

<!-- legacy-source:start:133:133 -->
## P1f'-pm (Tasaki §2.2): Total raising/lowering `Ŝ^±_tot = Σ_x Ŝ_x^±` (eq. (2.2.8))

Done
<!-- legacy-source:end:133:133 -->

<!-- legacy-source:start:134:134 -->
## P1f-mag (Tasaki §2.2): Total magnetization `|σ| := Σ_x spinSign(σ_x)` (eq. (2.2.2))

Done
<!-- legacy-source:end:134:134 -->

<!-- legacy-source:start:135:135 -->
## P1f'' (Tasaki §2.2): Global rotation `Û^(α)_θ = exp(-iθ Ŝ_tot^(α))` (eq. (2.2.11))

Done (proved without axioms)
<!-- legacy-source:end:135:135 -->

<!-- legacy-source:start:136:136 -->
## P1f''' (Tasaki §2.2): SU(2) / U(1) invariance (eqs. (2.2.12)-(2.2.13))

Done (commutativity `totalSpinHalfRot{α}_commute_of_commute`, unitarity
`totalSpinHalfRot{α}_conjTranspose_mul_self`, and finite-form invariance
`totalSpinHalfRot{α}_conj_eq_self_of_commute` all proved without axioms)
<!-- legacy-source:end:136:136 -->

<!-- legacy-source:start:137:137 -->
## P1f'''' (Tasaki §2.2): Two-site inner product `Ŝ_x · Ŝ_y` raising/lowering decomposition (eq. (2.2.16))

Done
<!-- legacy-source:end:137:137 -->

<!-- legacy-source:start:138:138 -->
## P1f''''' (Tasaki §2.2): SU(2) invariance of `Ŝ_x · Ŝ_y` and eigenvalues (eqs. (2.2.17)–(2.2.19))

Done
<!-- legacy-source:end:138:138 -->

<!-- legacy-source:start:139:139 -->
## P1f-2c (Tasaki §2.2 Problem 2.2.c): SU(2)-averaged two-site state = singlet projector (eq. (2.2.15)); integration over Euler angles `φ ∈ [0,2π]`, `θ ∈ [0,π]`

Done
<!-- legacy-source:end:139:139 -->

<!-- legacy-source:start:140:140 -->
## P1i (Tasaki §2.4): Heisenberg Hamiltonian on the fully-polarised state: `H |s…s⟩ = (∑_{x,y} J(x,y)·(if x=y then 3/4 else 1/4)) · |s…s⟩` (eq. (2.4.5), `S = 1/2`); plus the ladder step `Ŝ_tot^± · |s…s⟩` preserves the same H-eigenvalue (eqs. (2.4.7)/(2.4.9), `S = 1/2`) and its iterated form `(Ŝ_tot^±)^k · |s…s⟩` for every `k : ℕ`; plus `[H, Û^(α)_θ] = 0` for the global rotation (eq. (2.4.7) operator-level), the single-axis rotated constant-spin state `Û^(α)_θ · |s…s⟩` shares the H-eigenvalue, and the two-axis spin-coherent state `Û^(3)_ϕ Û^(2)_θ · |s…s⟩ = |Ξ_θ,ϕ⟩` (eq. (2.4.6) for `s = 0`); plus the magnetic-quantum-number labelling `Ŝtot^(3) · (Ŝtot^-)^k · |↑..↑⟩ = (Smax - k) · (Ŝtot^-)^k · |↑..↑⟩` (eq. (2.4.9), unnormalised, lowering from highest weight) and its dual `Ŝtot^(3) · (Ŝtot^+)^k · |↓..↓⟩ = (-Smax + k) · (Ŝtot^+)^k · |↓..↓⟩` (eq. (2.4.9), unnormalised, raising from lowest weight); plus the Casimir invariance `Ŝtot² · (Ŝtot^∓)^k · |s..s⟩ = Smax(Smax+1) · (Ŝtot^∓)^k · |s..s⟩` for any constant `s`. For the matched highest/lowest-weight ladders, the unnormalised iterates `(Ŝtot^-)^k · |↑..↑⟩` and `(Ŝtot^+)^k · |↓..↓⟩` carry `(H, Ŝtot², Ŝtot^(3))` simultaneous eigenvalues `(c_J, Smax(Smax+1), Smax∓k)`; plus the boundary annihilations `Ŝtot^- · |↓..↓⟩ = 0` and `Ŝtot^+ · |↑..↑⟩ = 0` ensuring the ladder terminates after spanning all `2Smax + 1 = |Λ| + 1` magnetisation sectors — building toward the full |Φ_M⟩ / |Ξ_θ,ϕ⟩ ferromagnetic ground-state space

Done
<!-- legacy-source:end:140:140 -->

<!-- legacy-source:start:141:141 -->
## P1g: Gibbs state `ρ = e^{-βH}/Z`, `Tr(ρ) = 1`, `⟨1⟩ = 1`, `Z(0) = dim`, `Z(0) ≠ 0`, linearity `⟨O₁+O₂⟩ = ⟨O₁⟩+⟨O₂⟩`, `⟨c·O⟩ = c·⟨O⟩`, `⟨-O⟩ = -⟨O⟩`, `⟨A−B⟩ = ⟨A⟩−⟨B⟩`, `⟨Σ f⟩ = Σ ⟨f⟩`, `[ρ, H] = 0`, reality of `⟨O⟩` for Hermitian `O`, conservation `⟨[H,A]⟩ = 0`, anticommutator real / commutator imaginary, `(⟨H·O⟩).im = 0`, β = 0 closed form `ρ_0 = I/dim` and `⟨A⟩_0 = Tr A / dim`, one-parameter group property `e^{-(β₁+β₂)H} = e^{-β₁H} · e^{-β₂H}` and invertibility, exact discrete semigroup identity `e^{-(nβ)H} = (e^{-βH})^n` (extended to `n : ℤ` via `gibbsExp_inv`)

Done
<!-- legacy-source:end:141:141 -->

<!-- legacy-source:start:142:142 -->
## P1h: Periodic boundary conditions, Heisenberg chain (open and periodic BC), Gibbs state instantiation for both BCs (Hermiticity, commutativity with `H`, β = 0 closed form, expectation realness for Hermitian observables, conservation `⟨[H, A]⟩ = 0`, energy expectation as a bond-sum decomposition, energy expectation real, `⟨H · O⟩` real for Hermitian `O`, `⟨H^n⟩` real for any `n : ℕ`)

Done
<!-- legacy-source:end:142:142 -->

<!-- legacy-source:start:143:143 -->
## P1j (Tasaki §2.3): Single-spin and multi-spin time-reversal map `Θ̂ := û_2 · K̂` for `S = 1/2`: explicit formula `Θ̂((a, b)ᵀ) = (-b*, a*)ᵀ` (Tasaki eq. (2.3.6)), action on `|ψ^↑⟩` / `|ψ^↓⟩`, additivity, antilinearity, single-spin **Kramers degeneracy** `Θ̂² = -1̂` (Tasaki eq. (2.3.8) at half-odd-integer spin), spin sign flip `Θ̂(Ŝ^(α) v) = -Ŝ^(α)(Θ̂ v)` (Tasaki eq. (2.3.14)), and multi-spin Kramers `Θ̂_tot² = (-1)^|Λ| · 1̂` for finite `Λ` (Tasaki §2.3 lattice extension at `S = 1/2`)

Done
<!-- legacy-source:end:143:143 -->
