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
`Real.sqrt`; `hvlPlusState_order_mean_ge_sqrt` takes assumption (3.4.4) in both its first- and
third-moment forms (`hodd1` and `hodd3`), and the capstone takes the same two odd-moment hypotheses
to assemble that lemma's conclusion into eq. (3.4.16)'s conjunct. The
Schwarz remark (3.4.17) holds for any normalised vector and is not used in the derivation of
eq. (3.4.16); Hermiticity of the order operator is essential there, since for a nilpotent operator
the right-hand side can vanish while the left-hand side does not.

The abstract layer takes the volume as a positive real parameter and the capstone instantiates it at
`L^d`, the same two-layer split as eq. (3.4.12). The `L ↑ ∞` and `h ↓ 0` limits of Theorem 3.2 are
taken in `Quantum/KaplanHorschVonderLindenTheorem32.lean` (below, "Theorem 3.2" section of this
part).

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

## The mirror state `Ξ₋` (pp. 68-69)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, the sentence
beginning "Of course the state `|Ξ₋⟩ = (|Φ_GS⟩ − |Γ⟩)/√2` ..." on p. 68, the same page as
eqs. (3.4.14) and (3.4.16).

`Quantum/HorschVonderLindenLowLyingState.lean` builds `Ξ₋` on top of the sign identity
`hvlTrialState_neg : Γ(−Ô_L) = −Γ(Ô_L)` (`Quantum/HorschVonderLindenTrialState.lean`): the
normalisation factor `‖Ô_L|Φ_GS⟩‖` is even in the sign of `Ô_L`, so mirroring the order operator
only flips the sign of the vector that factor scales. This gives the bridge
`hvlMinusState_eq_hvlPlusState_neg : Ξ₋(Ô_L) = Ξ₊(−Ô_L)`, needing neither Hermiticity of `Ô_L` nor
normalisation of `Φ_GS`. Four `Ξ₋` declarations below are obtained by instantiating their `Ξ₊`
counterpart at `−Ô_L`: normalisation (`hvlMinusState_dotProduct_self`, from
`hvlPlusState_dotProduct_self`, part 3, "Authoritative supplemental implementation record") and the
order mean (`hvlMinusState_order_mean`, from `hvlPlusState_order_mean`, same section of part 3), and
the energy identity (`hvlMinusState_energy_eq`, from `hvlPlusState_energy_eq`, part 4, "The
low-lying state `Ξ₊`") and the order bound (`hvlMinusState_order_mean_le_neg_sqrt`, from
`hvlPlusState_order_mean_ge_sqrt`, same section of part 4); the
mirror argument itself is never replayed there. The energy identity is **even** in the sign of the
trial state, so `⟨Ξ₋|Ĥ|Ξ₋⟩` reduces to the same right-hand side `(E_GS + ⟨Γ|Ĥ|Γ⟩)/2` as
`⟨Ξ₊|Ĥ|Ξ₊⟩`, while the order mean is **odd**, so its `Ξ₋` form carries a minus sign against
eq. (3.4.16). Orthogonality `⟨Ξ₋|Ξ₊⟩ = 0` is proved separately from the `Γ` moment algebra rather
than by substitution — a pairing of two different states has no single-state `Ξ₊` counterpart to
instantiate — from the diagonal terms `⟨Φ_GS|Φ_GS⟩ = 1` and `⟨Γ|Γ⟩ = 1` cancelling against each
other and both cross terms vanishing by the first odd-moment assumption (3.4.4), together with the
normalisation of `Φ_GS` and of `Γ`. The capstone `tasaki_mirrorLowLyingState_ssb` is likewise not
among the four: it calls the `Ξ₊` capstone at `+Ô_L` and transports its energy conjuncts across the
energy identity `⟨Ξ₋|Ĥ|Ξ₋⟩ = ⟨Ξ₊|Ĥ|Ξ₊⟩`, so eq. (3.4.12) is not re-derived.

**Corrigendum (printed sub/superscript, not load-bearing).** The orthogonality sentence on p. 68
names the state `|Ξ_L^+⟩`, carrying an `L` subscript this symbol carries nowhere else in §3.4 and
placing the `+` in superscript where the surrounding text (including eq. (3.4.14) itself) places
it in subscript, `|Ξ_+⟩`. Under either reading the referent is the same state, the one of
eq. (3.4.14); no value or derivation in this repository depends on which reading is intended.
`hvlMinusState_dotProduct_hvlPlusState` below states orthogonality against `hvlPlusState`, the
eq. (3.4.14) state.

**What these declarations do not assert.** Hermiticity of `Ô_L` is not assumed by
`hvlTrialState_neg` or the bridge; it first enters through the instantiation at `−Ô_L`, in each of
the four `Ξ₋` declarations named above, and separately, directly at `+Ô_L` (not through any
instantiation), in the orthogonality proof `hvlMinusState_dotProduct_hvlPlusState`
(`Quantum/HorschVonderLindenLowLyingState.lean:331`). The `L ↑ ∞` and `h ↓ 0` limits of Theorem 3.2
are taken in `Quantum/KaplanHorschVonderLindenTheorem32.lean` (below, "Theorem 3.2" section of this
part), but the mirror state `Ξ₋` does not enter there: the capstone's trial-state hypothesis is
eq. (3.4.16) at `Ξ₊`, not its mirror form.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `hvlTrialState_neg` | `Γ(−Ô_L) = −Γ(Ô_L)`, the trial state is odd in the order operator; no hypothesis | `Quantum/HorschVonderLindenTrialState.lean` |
| `hvlMinusState` | the mirror state `\|Ξ₋⟩ = (1/√2)(\|Φ_GS⟩ − \|Γ⟩)`, pp. 68-69 | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlMinusState_eq_hvlPlusState_neg` | the mirror bridge `Ξ₋(Ô_L) = Ξ₊(−Ô_L)`; no hypothesis | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlMinusState_dotProduct_self` | `⟨Ξ₋\|Ξ₋⟩ = 1`, from `hvlPlusState_dotProduct_self` at `−Ô_L`, under Hermiticity, normalisation, the first odd moment and `0 < m₂` | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlMinusState_energy_eq` | `⟨Ξ₋\|Ĥ\|Ξ₋⟩ = (E_GS + ⟨Γ\|Ĥ\|Γ⟩)/2`, from `hvlPlusState_energy_eq` at `−Ô_L`, under Hermiticity of `Ĥ` and `Ô_L`, the eigenvector hypothesis, normalisation and the first odd moment | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlMinusState_order_mean` | `⟨Ξ₋\|Ô_L\|Ξ₋⟩ = −√m₂`, from `hvlPlusState_order_mean` at `−Ô_L`, under Hermiticity, the first and third odd moments and `0 < m₂` | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlMinusState_order_mean_le_neg_sqrt` | the mirror form of eq. (3.4.16), `⟨Ξ₋\|Ô_L\|Ξ₋⟩ / Ld ≤ −√q₀`, from `hvlPlusState_order_mean_ge_sqrt` at `−Ô_L`, under Hermiticity, the first and third odd moments, `0 < q₀`, `0 < Ld` and long-range order | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `hvlMinusState_dotProduct_hvlPlusState` | orthogonality `⟨Ξ₋\|Ξ₊⟩ = 0`, proved from the `Γ` moment algebra, under Hermiticity, normalisation, the first odd moment and `0 < m₂` | `Quantum/HorschVonderLindenLowLyingState.lean` |
| `tasaki_mirrorLowLyingState_ssb` (**capstone**) | the mirror-state sentence of p. 68 in the bond-local spin-`S` setting: `⟨Ξ₋\|Ξ₋⟩ = 1`, `⟨Ξ₋\|Ξ₊⟩ = 0`, `0 ≤ ⟨Ξ₋\|Ĥ\|Ξ₋⟩ − E_GS ≤ (C/2) L^{-d}` with `C = 8 d h₀ o₀² / q₀`, and `⟨Ξ₋\|Ô_L/L^d\|Ξ₋⟩ ≤ −√q₀`, under the same hypothesis block as `tasaki_eq_3_4_16_lowLyingState_ssb` | `Quantum/HorschVonderLindenLowLyingState.lean` |

**Boundary facts, checked against the tree.** At the concrete one-dimensional instance `Ô_L = 0`
the order-square Rayleigh quotient `⟨Φ_GS|(Ô_L)²|Φ_GS⟩` vanishes, `Γ` is the zero vector, and `Ξ₋`
coincides with `Ξ₊`: the positivity hypothesis `0 < m₂` taken by `hvlMinusState_dotProduct_self`
and `hvlMinusState_dotProduct_hvlPlusState` is therefore a **truth condition** for normalisation
and orthogonality at this instance, not proof convenience — `⟨Ξ₋|Ξ₋⟩` and `⟨Ξ₋|Ξ₊⟩` both come out
`1/2` rather than `1` and `0`. The energy identity still holds at that same degenerate instance
(`Ô_L = 0`, `Ĥ = diagonal ![5]`); the fixture pins the identity itself, not a bare numeric value. A
negative size parameter falsifies the mirror order bound: at `Ld = −2` with `q₀ = 1` the conclusion
of `hvlMinusState_order_mean_le_neg_sqrt` fails; the fixture pins that failure but not that the
remaining hypotheses (in particular the long-range-order hypothesis) hold at this data. Argued but
**not** machine-checked in this repository: that the long-range-order hypothesis of
`hvlMinusState_order_mean_le_neg_sqrt` also holds at `Ld = −2`, `q₀ = 1`; whether `Γ` is the zero
vector, and `Ξ₋` coincides with `Ξ₊`, at every vanishing order-square Rayleigh quotient, beyond the
one instance `Ô_L = 0` checked; whether `hvlMinusState_order_mean_le_neg_sqrt` fails at every
negative `Ld` (checked only at `Ld = −2`); the vacuity/falsity distinction at `d = 0`, where the
bond-set hypothesis forces the constant `C` to `0` and the energy conjuncts of the capstone read
`0 ≤ 0 ≤ 0` while the normalisation, orthogonality and order conjuncts keep content.

Regression fixtures live in `LatticeSystem/Tests/HorschVonderLindenLowLyingState.lean`, in the
block "Signature pins — the mirror state" and the "Sign-error fixtures for the mirror state `Ξ₋`"
that follow it. Because `Ξ₋` differs from `Ξ₊` only by signs, a fixture built for `Ξ₊` can pass on
a wrongly-signed `Ξ₋`, so each numeric fixture carries a value that discriminates the correct sign:
a direct pin on the state's four entries on the two-spin instance
(`hvlMinusState fO fPhi = ![1/2, -(1/2), -(1/2), 1/2]`); the energy identity together with the
sign-discriminating value `rayleighOnVec fO (hvlMinusState fO fPhi) = -2` against `Ξ₊`'s `+2`
(needed because the identity's own right-hand side is even in the sign of `Γ` and would not by
itself catch a flipped sign); orthogonality and normalisation pinned together, since substituting
`Ξ₊` for `Ξ₋` there reads `1 = 0`; a tight instance at `q₀ = 1`, `Ld = 2`; a negative-`Ld` instance
where the mirror bound's own conclusion fails; two boundary instances at a vanishing
order-square Rayleigh quotient, discharged by proof rather than assumed satisfiable; and a mirror
capstone non-vacuity witness at the same data as the `Ξ₊` capstone's, showing
`tasaki_mirrorLowLyingState_ssb` is not vacuously true for every instance.

## Theorem 3.2 (Kaplan–Horsch–von der Linden), eqs. (3.4.21)-(3.4.22)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, eq. (3.4.12)
p. 67, eq. (3.4.16) p. 68, Theorem 3.2 with footnote 24 and eqs. (3.4.19)-(3.4.22), pp. 69-70.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `tasaki_eq_3_4_21_perVolume` | eq. (3.4.21)'s printed second line, per volume: the finite-volume variational bound divided through by a volume `Ld > 0`, with the trial-state order mean carried abstractly via `hXi` | `Quantum/KaplanHorschVonderLindenTheorem32.lean` |
| `tasaki_eq_3_4_21_perVolume_energyBound` | the same per-volume bound with the halved eq. (3.4.12) trial-energy bound made explicit, giving the `L^{2d}` error denominator | `Quantum/KaplanHorschVonderLindenTheorem32.lean` |
| `tasaki_orderParameter_uniformBound` | the order parameter per volume is bounded by a per-site operator-norm bound, given a carrier hypothesis `#Λ ≤ L^d` | `Quantum/KaplanHorschVonderLindenTheorem32.lean` |
| `tasaki_eq_3_4_21_volumeLiminf` | the inner `L ↑ ∞` limit of eq. (3.4.22): `m ≤ liminf_{L↑∞} ⟨Ψ L\|O L\|Ψ L⟩/L^d` | `Quantum/KaplanHorschVonderLindenTheorem32.lean` |
| `tasaki_theorem_3_2_kaplanHorschVonderLinden` (**capstone**) | eq. (3.4.22): `√q₀ ≤ liminf_{h↓0} liminf_{L↑∞} ⟨Ψ h L\|O L\|Ψ h L⟩/L^d`, both limits `Filter.liminf` per footnote 24, in the printed order | `Quantum/KaplanHorschVonderLindenTheorem32.lean` |

Eq. (3.4.21) is the variational core (`kaplan_horsch_vonderLinden_order_lower_bound`,
`Quantum/KaplanHorschVonderLinden.lean`) divided by the volume and read against eq. (3.4.16) at the
trial state `Ξ₊`: the order-parameter bound of eq. (3.4.16) supplies the lower bound `hXi` that the
per-volume statement takes abstractly. Feeding the halved eq. (3.4.12) energy bound
`⟨Ξ₊|Ĥ|Ξ₊⟩ − E_GS ≤ (C/2)L^{-d}` in place of the abstract error term turns the correction into an
`L^{2d}` term, because the energy bound supplied is itself of order `L^{-d}`: one factor of
`L^{-d}` comes from that bound and a second from dividing the order parameter by the volume.
Eq. (3.4.22) is stated with `Filter.liminf` in both limits per footnote 24 (p. 70), and in the
printed order: the inner limit over the volume index `L` along `atTop`, the outer limit over the
field strength `h` along `𝓝[>] 0`. The order is not cosmetic: a fixture in
`LatticeSystem/Tests/KaplanHorschVonderLindenTheorem32.lean` evaluates both nestings on the bounded
family `min (h·L) 1` and pins the printed-order value at `1` and the exchanged-order value at `0`.
That family is not an instance of the capstone's data, so what is machine-checked there is the
separation of the two nestings, not the falsity of the capstone with its limits exchanged.

**What these declarations do not assert.** The `L`-indexed and `h`-indexed family is carried as
abstract per-volume matrices; a spin-`S` family whose vertex set grows with the volume is not built
here. The trial states reach the Theorem 3.2 capstone only through the eq. (3.4.16) order bound and
the halved eq. (3.4.12) energy bound: of the `Ξ₊` capstone's four conjuncts only those two become
hypotheses there, the normalisation and the lower energy conjunct do not. The perturbed states
reach it through eq. (3.4.20), a lower bound on their Rayleigh energy, and the uniform order bound;
the dimension enters through `1 ≤ d`. The limiting state the
source discusses after Theorem 3.2 is not constructed. The uniform bound needs a carrier hypothesis
`#Λ ≤ L^d` that eq. (3.4.12)'s bond-count hypothesis does not supply.

---

[← Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1)](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-03/) · [Catalogue](/lattice-system/formalization/legacy/) · [Bose–Einstein condensation of hard-core bosons (Tasaki §5.1–§5.2) →](/lattice-system/formalization/legacy/17-bose-einstein-condensation-of-hard-core-bosons-tasaki-5-1-/)
