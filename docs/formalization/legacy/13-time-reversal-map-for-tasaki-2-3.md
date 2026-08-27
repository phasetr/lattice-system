---
layout: page
title: "Legacy catalogue: Time-reversal map for `S = 1/2` (Tasaki §2.3)"
permalink: /formalization/legacy/13-time-reversal-map-for-tasaki-2-3/
---

# Legacy catalogue: Time-reversal map for `S = 1/2` (Tasaki §2.3)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:467:505 -->
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
| `timeReversalSpinHalfMulti_onSite_pauliZ_mulVec` | multi-site sign-flip equivariance for `σ^z` (Tasaki §2.3 (2.3.14) lifted to many-body): `Θ̂_tot ((onSite x σ^z) v) = (-(onSite x σ^z))(Θ̂_tot v)`. Diagonal-action case; `σ^x`, `σ^y` deferred | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `siteFlipAt` / `siteFlipAt_self` / `siteFlipAt_of_ne` / `flipConfig_siteFlipAt_comm` / `siteFlipAt_involutive` | per-site flip helpers: `siteFlipAt τ x` flips slot `x` only; commutes with `flipConfig`; involutive. The combinatorial primitive underlying off-diagonal `σ^x_x` / `σ^y_x` action (deferred) | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `onSite_pauliX_mulVec_basisVec` | basis-state action of the off-diagonal site Pauli: `(onSite x σ^x).mulVec |Ψ_σ⟩ = |Ψ_{siteFlipAt σ x}⟩` (the spin at site `x` is swapped) | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `pauliX_eq_indicator` / `onSite_pauliX_mulVec_apply` | closed-form `pauliX a b = if b = 1 - a then 1 else 0`, lifted to `((onSite x σ^x).mulVec v) τ = v (siteFlipAt τ x)` for any state `v` (general extension of the basis-state action) | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `timeReversalSign_prod_siteFlipAt` | `∏_y ε((siteFlipAt τ x) y) = -(∏_y ε(τ y))` — the per-site flip swaps `ε(τ x)` with `ε(1 - τ x) = -ε(τ x)`, flipping the total sign | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `timeReversalSpinHalfMulti_onSite_pauliX_mulVec` | multi-site sign-flip equivariance for `σ^x` (Tasaki §2.3 (2.3.14) at α = 1): `Θ̂_tot ((onSite x σ^x) v) = (-(onSite x σ^x))(Θ̂_tot v)` | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `timeReversalSpinHalfMulti_onSite_pauliY_mulVec` | multi-site sign-flip equivariance for `σ^y` (Tasaki §2.3 (2.3.14) at α = 2): `Θ̂_tot ((onSite x σ^y) v) = (-(onSite x σ^y))(Θ̂_tot v)`. The proof handles the per-site `±i` factor via `conj(pauliY_sign(1 - s)) = pauliY_sign(s)` | `Quantum/TimeReversalMulti/SpinOpEquivariance.lean` |
| `timeReversalSpinHalfMulti_add` / `_smul` / `_real_smul` | multi-spin `Θ̂_tot` is additive, antilinear in the scalar (`Θ̂_tot(c • v) = conj(c) • Θ̂_tot v`), and real-linear (special case of antilinearity at real `r`) — foundational for lifting Pauli-axis equivariance to bilinear / Heisenberg-type Hamiltonian forms | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_onSite_spinHalfOp{1,2,3}_mulVec` | Tasaki §2.3 (2.3.14) for spin-1/2 ops `Ŝ^(α) = σ^(α) / 2`: `Θ̂_tot ((onSite x Ŝ^(α)) v) = (-(onSite x Ŝ^(α)))(Θ̂_tot v)` for α = 1, 2, 3 — direct corollaries of the Pauli versions by scalar (1/2) multiplication | `Quantum/TimeReversalMulti.lean` |
| `timeReversalSpinHalfMulti_spinHalfDot_mulVec` | **Time-reversal invariance of the bilinear `Ŝ_x · Ŝ_y`** (Tasaki §2.3): `Θ̂_tot ((Ŝ_x · Ŝ_y) v) = (Ŝ_x · Ŝ_y)(Θ̂_tot v)` — two equivariance `-1` factors cancel; sums per-axis | `Quantum/TimeReversalMulti/Heisenberg.lean` |
| `timeReversalSpinHalfMulti_heisenbergHamiltonian_mulVec` | **Time-reversal invariance of the Heisenberg Hamiltonian** (Tasaki §2.3): for real coupling `J` (`conj(J(x,y)) = J(x,y)`), `Θ̂_tot ((H J) v) = (H J)(Θ̂_tot v)`. Combines per-bond invariance + Θ̂_tot antilinearity (J reality) + additivity (over double-sum) | `Quantum/TimeReversalMulti/Heisenberg.lean` |
| `openChainCoupling_conj` / `periodicChainCoupling_conj` | every entry of `openChainCoupling N J` (resp. `periodicChainCoupling N J`) is real (under complex conjugation), since `J : ℝ` makes `(-(J : ℂ))` real-valued | `Quantum/HeisenbergChain.lean` |
| `timeReversalSpinHalfMulti_openChainHeisenberg_mulVec` / `_periodicChainHeisenberg_mulVec` / `_squareLatticeHeisenberg_mulVec` / `_squareTorusHeisenberg_mulVec` / `_cubicLatticeHeisenberg_mulVec` | concrete time-reversal invariance: the open / periodic chain, the 2D open square / torus, and the 3D cubic Heisenberg Hamiltonians all commute with `Θ̂_tot` for any real coupling `J : ℝ`. Backed by `*Coupling_conj` reality lemmas in `HeisenbergChain.lean` | `Quantum/TimeReversalMulti/Heisenberg.lean` |
| `timeReversalSpinHalfMulti_basisVec_upDown` / `_basisVec_basisSwap_upDown` | `Θ̂_tot |↑↓⟩ = -|↓↑⟩` and `Θ̂_tot |↓↑⟩ = -|↑↓⟩` on `Fin 2` | `Quantum/TimeReversalMulti/Heisenberg.lean` |
| `timeReversalSpinHalfMulti_singlet` | the two-site spin singlet `|↑↓⟩ - |↓↑⟩` is **time-reversal invariant** (Tasaki §2.3 / §A.3): being the SU(2) `S = 0` representation, it survives `Θ̂_tot` unchanged | `Quantum/TimeReversalMulti/Heisenberg.lean` |
| `timeReversalSpinHalfMulti_triplet_zero` | the triplet `m = 0` state `|↑↓⟩ + |↓↑⟩` is **anti-invariant** under `Θ̂_tot`: `Θ̂_tot (|↑↓⟩ + |↓↑⟩) = -(|↑↓⟩ + |↓↑⟩)` (the symmetric combination picks up a minus sign from the per-basis-vector flip) | `Quantum/TimeReversalMulti/Heisenberg.lean` |

<!-- legacy-source:end:467:505 -->

## Authoritative supplemental implementation record (Problem 2.3.a Kramers orthogonality)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline; it is not subject to the frozen byte-for-byte
parity of the block above.

| Lean name | Statement | File |
|---|---|---|
| `inner_timeReversal_eq_zero_of_sq_neg` | **Problem 2.3.a: Kramers-degeneracy orthogonality for an inner-product-reversing square-root-of-`-1̂`** (**PROVED**, `#print axioms` = std3; Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 2.3.a, p. 31, solution p. 496; Appendix A.4.3 eq. (A.4.17)): for a map `V` on a complex inner product space with `⟪V u, V v⟫ = ⟪v, u⟫` for all `u, v` and `V (V v) = -v`, every vector `v` is orthogonal to its image, `⟪v, V v⟫ = 0`; neither linearity nor antilinearity of `V` is assumed, whereas Tasaki's antiunitary operators of eq. (A.4.17) are antilinear by definition — the general half-odd-integer-spin Kramers-degeneracy orthogonality argument, stated for such an abstract `V` rather than the concrete `Θ̂` of `timeReversalSpinHalf` | `Quantum/TimeReversalSpinHalf.lean` |

---

[← Basis states and raising/lowering for S = 1 (Tasaki §2.1)](/lattice-system/formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1/) · [Catalogue](/lattice-system/formalization/legacy/) · [Multi-body operator space (abstract lattice) →](/lattice-system/formalization/legacy/14-multi-body-operator-space-abstract-lattice/)
