---
layout: page
title: "Legacy catalogue: Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) (part 4 of 4)"
permalink: /formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-04/
---

# Legacy catalogue: Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) (part 4 of 4)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

## The low-lying state `Ξ₊`, eqs. (3.4.16)-(3.4.17)

This section is maintained by hand, lies outside the migrated catalogue block, and records
declarations added after the migration baseline; it is not subject to the frozen byte-for-byte
parity of the migrated block.


Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, "Setting and
assumptions" and eq. (3.4.3) p. 65, eq. (3.4.12) p. 67, eqs. (3.4.14)-(3.4.16) p. 68, the Schwarz
remark eq. (3.4.17) p. 69.

`Quantum/HorschVonderLindenLowLyingState.lean` carries the sentence of p. 68 that `|Ξ₊⟩` "is a
low-lying state" which "exhibits symmetry breaking": the normalisation `⟨Ξ₊|Ξ₊⟩ = 1`, the two-sided
energy bound `0 ≤ ⟨Ξ₊|Ĥ|Ξ₊⟩ − E_GS ≤ (C/2) L^{-d}` with the `C = 8 d h₀ o₀² / q₀` of eq. (3.4.12),
and eq. (3.4.16) `⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀`. The capstone `tasaki_eq_3_4_16_lowLyingState_ssb` states
these as four conjuncts (normalisation; `0 ≤ ⟨Ξ₊|Ĥ|Ξ₊⟩ − E_GS`; `≤ (C/2) L^{-d}`; eq. (3.4.16)) in
the bond-local spin-`S` setting of eqs. (3.4.1)-(3.4.2).

The factor `C/2` is not an estimate: `⟨Ξ₊|Ĥ|Ξ₊⟩ = (E_GS + ⟨Γ|Ĥ|Γ⟩)/2` exactly, because both cross
terms vanish — `Φ_GS` is an eigenvector of the Hermitian `Ĥ` and `⟨Φ_GS|Γ⟩ = 0` by the no-SSB
assumption (3.4.4). That identity is the step the source covers with the word "obviously"; it needs
no positivity of the second moment, and at a vanishing second moment `Γ` is the zero vector and the
identity still holds. Eq. (3.4.16) is eq. (3.4.15) read against eq. (3.4.3) through monotonicity of
`Real.sqrt`; `hvlPlusState_order_mean_ge_sqrt` takes assumption (3.4.4) in its third-moment form
(the vanishing of `⟨Φ_GS|(Ô_L)³|Φ_GS⟩`), and the capstone takes the same third-moment hypothesis to
assemble that lemma's conclusion into eq. (3.4.16)'s conjunct. The
Schwarz remark (3.4.17) holds for any normalised vector and is not used in the derivation of
eq. (3.4.16); Hermiticity of the order operator is essential there, since for a nilpotent operator
the right-hand side can vanish while the left-hand side does not.

The abstract layer takes the volume as a positive real parameter and the capstone instantiates it at
`L^d`, the same two-layer split as eq. (3.4.12). The `L ↑ ∞` and `h ↓ 0` limits of Theorem 3.2 are
not taken.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `hvlPlusState_energy_eq` | `⟨Ξ₊\|Ĥ\|Ξ₊⟩ = (E_GS + ⟨Γ\|Ĥ\|Γ⟩)/2` for an eigenvector `Φ_GS` of a Hermitian `Ĥ`, under normalisation and the first odd-moment vanishing (3.4.4) | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlPlusState_order_mean_ge_sqrt` | eq. (3.4.16) with the volume as a positive real parameter: `√q₀ ≤ ⟨Ξ₊\|Ô_L\|Ξ₊⟩ / Ld` from eq. (3.4.3) | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `tasaki_eq_3_4_17_order_mean_abs_le_sqrt` | eq. (3.4.17): `\|⟨Φ\|Ô_L/Ld\|Φ⟩\| ≤ √(⟨Φ\|(Ô_L/Ld)²\|Φ⟩)` for any normalised `Φ` and Hermitian `Ô_L` | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `tasaki_eq_3_4_16_lowLyingState_ssb` (**capstone**) | the low-lying state with LRO and SSB of p. 68: `⟨Ξ₊\|Ξ₊⟩ = 1`, `0 ≤ ⟨Ξ₊\|Ĥ\|Ξ₊⟩ − E_GS ≤ (C/2) L^{-d}` with `C = 8 d h₀ o₀² / q₀`, and eq. (3.4.16), in the bond-local spin-`S` setting of eqs. (3.4.1)-(3.4.2) | `Quantum/HorschVonderLindenLowLyingState.lean` |

Regression fixtures live in `LatticeSystem/Tests/HorschVonderLindenLowLyingState.lean`: signature
pins on the four declarations (the energy-identity pin fixing that no second-moment positivity
hypothesis appears, the eq. (3.4.16) pin fixing that no normalisation hypothesis appears, and the
capstone pin fixing the literal `4 d h₀ o₀² / q₀ / L^d` together with the two odd-moment hypotheses
that eq. (3.4.12) does not take); a concrete two-spin instance on `Fin 4` with a diagonal
Hamiltonian `diagonal ![-1,3,3,-1]` and a transverse order operator, whose (3.4.4) hypotheses are
*discharged by proof*, where `E_GS = -1`, `⟨Γ\|Ĥ\|Γ⟩ = 3`,
`⟨Ξ₊\|Ĥ\|Ξ₊⟩ = 1` separate the halved
identity from the un-halved, the `E_GS`-free and the sign-flipped shapes, and where eq. (3.4.16) is
*tight* at `q₀ = 1`, `L^d = 2`; three eq. (3.4.17) instances, a strict rational one, the same
instance at a negative size parameter (proved directly, since the declaration's own `0 < Ld`
hypothesis does not apply there), and a tight one at an eigenvector of the order operator; and a
capstone satisfiability witness (`Λ = Fin 1`, `N = 1`, `B = ∅`, single-site Pauli `X` as the order
operator) whose hypothesis bundle is discharged by proof, showing the capstone is not vacuously
true for every instance. Since a one-sided numeric endpoint is blind to a wrongly large right-hand
side, the strict eq. (3.4.17) instance routes through an intermediate step that spells the constant
and the radicand out syntactically.

---

[← Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1)](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-03/) · [Catalogue](/lattice-system/formalization/legacy/) · [Bose–Einstein condensation of hard-core bosons (Tasaki §5.1–§5.2) →](/lattice-system/formalization/legacy/17-bose-einstein-condensation-of-hard-core-bosons-tasaki-5-1-/)
