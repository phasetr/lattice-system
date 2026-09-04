---
layout: page
title: "Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 1"
permalink: /formalization/legacy/details/group-spin-models-part-01/
---

# Legacy long-form records: Spin models, Chapters 3–7, and spectral tools, part 1

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-560"></a>
## Record from former line 560

**Lean name:** <!-- legacy-detail-lean:start:560 -->`shastry_no_symmetry_breaking_1d`<!-- legacy-detail-lean:end:560 -->

**File:** <!-- legacy-detail-file:start:560 -->`Quantum/SpinS/ShastryNoSSB.lean`, `Quantum/SpinS/RingBondReflection.lean`, `Quantum/SpinS/RingReflectionTheta.lean`, `Quantum/SpinS/RingReflectionHamiltonian.lean`, `Quantum/SpinS/RingReflectionPositivity.lean`, `Quantum/SpinS/RingReflectionTraceCone.lean`, `Quantum/SpinS/RingReflectionWeightedCone.lean`, `Quantum/SpinS/RingReflectionGibbsCone.lean`, `Quantum/SpinS/RingReflectionGibbsExp.lean`, `Quantum/SpinS/RingReflectionExpSupport.lean`, `Quantum/SpinS/RingReflectionTwoFieldPairing.lean`, `Quantum/SpinS/RingReflectionRPDecomposition.lean`<!-- legacy-detail-file:end:560 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:560 -->
**Theorem 4.2** (§4.1, Shastry, DOCUMENTED AXIOM;

eqs. (4.1.9)–(4.1.10)): absence of SSB in 1D. **Tasaki §4.1 footnote 3 (p. 76) explicitly states "We
do not prove Theorem 4.2 in the present book" and refers to Shastry [58] (J. Phys. A 1992) and
Tanaka–Takeda–Idogaki [63] (JMMM 2004);

hence Thm 4.2 is a cite-only documented axiom (confirmed, not in-progress).** For the 1D AFM
Heisenberg ring under a staggered field `Ĥ_h = Σ_x Ŝ_x·Ŝ_{x+1} − h·Ô_L^(3)`, the per-site staggered
order parameter of any normalized ground state vanishes in the iterated limit `lim_{h↓0} lim_{L↑∞}`
(eq. (4.1.10), ε–δ form). We record it as a faithful documented axiom over the concrete ring family;

the deep infinite-volume argument is faithfully axiomatized (not re-proved). The
**reflection-positivity infrastructure project** (#4777, closed 2026-07-11 and historical)
formalized supporting finite-dim RP layers for the Cor 4.3 **conditional reduction**
(susceptibility no-LRO) and related Thm 4.2 RP auxiliary results — not a re-proof of Thm 4.2
itself, and not a discharge of Cor 4.3: that reduction and the documented axiom it consumed have
since been deleted, Cor 4.3 now following Tasaki's own contraposition from Thm 4.2 for all three
Cartesian axes, which leaves both open. Issue #5413, previously named as the successor discharge
issue, is closed as not planned. Defines
`ringCoupling`, `ringStaggeredSublattice`,
`staggeredFieldChainHamiltonianS`. **RP infra layer 1 (in progress):** `RingBondReflection.lean` —
even-ring bond reflection `ringReflect n x = 2n−1−x` (involutive, half-swap, staggered-sign flip);

`RingReflectionTheta.lean` — reflection map `θ(A) σ τ = conj(A(ρσ)(ρτ))`, an antilinear
`*`-automorphism, with the single-site bridge `θ(onSiteS x A) = onSiteS (ringReflect n x) (conj A)`.
**RP infra layer 2** (`RingReflectionHamiltonian.lean`): the Hamiltonian θ-decomposition —
orientation reversal `J(r x)(r y)=J y x`, spin-op conjugation (S¹/S³ real, S² imaginary),
`θ(Ŝ_x·Ŝ_y)=Ŝ_{r x}·Ŝ_{r y}`, `θ(Ô_L^(3))=−Ô_L^(3)` (staggered-sign flip), `θ(Ĥ)=Ĥ` (reindex +
adjacency + dot-comm), and `θ(Ĥ_h)=Ĥ_{−h}` (the reflection symmetry exchanging the two staggered
ground states). **RP infra layer 3** (`RingReflectionPositivity.lean`): the left-half subalgebra
`SupportedOnLeftS` = `B(H_left) ⊗ I_right` (two conditions: entries vanish off the right-diagonal
**and** are independent of the common right-half value) with closure (zero/one/add/smul, left-site
`onSiteS`), `θ` maps left-supported to right-supported (`theta_right`), and the reflection-positive
functional predicate `ReflectionPositiveFunctionalS` (`0 ≤ Re φ(θ(A)·A)` for left-supported `A`).
**RP infra layer 4** (`RingReflectionTraceCone.lean`): the `β = 0` base case —
`traceFunctional_reflectionPositive` proves the trace functional `X ↦ Tr X` is reflection positive,
i.e. `0 ≤ Re Tr(θ(A)·A)` for every left-supported `A`. The proof collapses `Tr(θ(A)·A) = ∑_{σ,μ}
θ(A)σμ·Aμσ` to its diagonal (both support conditions force `μ=σ`), then factorizes over the
left/right configuration split (`configSplitEquiv`, from `finSumFinEquiv`): the diagonal value `A σ
σ` depends only on the left half, giving `Tr(θ(A)·A) = conj S · S = ‖S‖² ≥ 0` with `S = ∑_ℓ D ℓ`.
This is the infinite-temperature trace cone on which a later layer mounts the Gibbs exponential via
Trotter. **RP infra layer 5** (`RingReflectionWeightedCone.lean`): the algebraic completion of the
cone — `SupportedOnLeftS.mul` (the left-half subalgebra is closed under products),
`SupportedOnLeftS.mul_theta_comm` (a left-supported `A` commutes with `θ(B)`, which acts on the
right half), and the **weighted trace cone** `weightedTraceFunctional_reflectionPositive` (`X ↦
Tr((θ(C)·C)·X)` is reflection positive for left-supported `C`, via `Tr((θC·C)·(θA·A)) =
Tr(θ(C·A)·(C·A)) ≥ 0`) plus its nonnegative-finite-combination version
`weightedTraceFunctional_reflectionPositive_finsetSum` — the cone on which the Trotter/Lie-product
factors of the Gibbs exponential will be mounted. **RP infra layer 6**
(`RingReflectionGibbsCone.lean`): the reflection-positive trace-weight cone — `RPTraceWeightS M` (`X
↦ Tr(M·X)` is an RP functional), the cone-representability predicate `RPTraceConeRepS` (nonnegative
finite combination `∑ cᵢ θ(Cᵢ)·Cᵢ`) with closure under `one`/`zero`/`add`/`smul_nonneg`/`mul`/`pow`,
with the product closure via the **four-operator generalization** `weightGen_mul`:
`(θ(A)·B)·(θ(A')·B') = θ(A·A')·(B·B')` (weakest hypotheses: only `B, A'` need be left-supported;

`A, B'` unconstrained;

specializes to `(θC·C)(θD·D) = θ(CD)·(CD)` for the diagonal cone;

the off-diagonal `A ≠ B` case closes the field-crossing product of `RPTwoFieldConeRepS.mul`).
**Field-dependent crossing cone:** `RPTwoFieldConeRepS n N P` (field-dependent two-field cone
representation: a field-independent index `ι` with nonnegative weights `c`, field-dependent
generators `C i z` (left-supported at each field), such that `P u v = ∑ᵢ cᵢ • (θ(C i v) · C i u)`
for every field pair;

diagonal `u = v` is a genuine cone;

off-diagonal `u ≠ v` is the field-crossing form) with closure under
`one`/`zero`/`add`/`smul_nonneg`/`mul`/`pow`/`expSeriesPartialSum` (fieldwise from the
field-independent cone operations) where the field-free `RPTraceConeRepS` embeds as the constant
family `C i z := Ĉ i` (recovered as the `u = v`, constant-in-field degenerate case — not a
duplicate). These give the shared field-crossing cone family that the three slots of the two-field
reflection Cauchy–Schwarz of Tasaki (4.1.51)/(4.1.69) (pp. 89–93;

DLS 1978 §2–3) consume. Additional: `RPTraceConeRepS.rpTraceWeight` (representable ⟹ RP trace
weight, from the weighted cone), and `RPTraceWeightS.tendsto` (RP trace weights are closed under
limits, by finite-dimensional trace continuity) — the cone on which the next layer mounts the
interaction Gibbs exponential `exp(t·∑cᵢθ(Cᵢ)·Cᵢ)` as a limit of cone-representable partial sums (PR
#4991). **RP infra layer 7** (`RingReflectionGibbsExp.lean`): `rpInteractionExp_reflectionPositive`
— for a nonnegative finite interaction `D = t·∑ᵢ cᵢ θ(Cᵢ)·Cᵢ` (`t, cᵢ ≥ 0`, `Cᵢ` left-supported),
the matrix exponential `exp D` is a reflection-positive trace weight. Each partial sum
`∑_{k<m}(k!)⁻¹Dᵏ` of the exponential series is cone-representable (`smul_nonneg`/`add`/`pow`), hence
an RP trace weight, and `exp D` is their limit (`expSeries_summable'.hasSum.tendsto_sum_nat`), so
`RPTraceWeightS.tendsto` applies. Uses the `L∞`-operator-norm Banach structure (`open scoped
Matrix.Norms.Operator`), whose topology is the entrywise (Pi) topology — the same one underlying the
trace continuity, so no topology diamond. **RP infra layer 8** (`RingReflectionExpSupport.lean`):
the matrix exponential and the left subalgebra / reflection map — `SupportedOnLeftS.exp` (`X`
left-supported ⟹ `exp X` left-supported: the left subalgebra is closed under
products/sums/scalars/entrywise-limits via `SupportedOnLeftS.of_tendsto`, and `exp X` is the limit
of its partial sums) and `ringReflectionThetaS_exp` (`θ(exp X) = exp(θ X)`: `θ` is a continuous
conjugate-linear `*`-automorphism with real exponential coefficients) — the building blocks for the
`e^{-βH_L}` Hamiltonian factor of the full Gibbs reflection-positivity decomposition
<!-- legacy-detail:end:560 -->

**Correction addendum (outside the frozen block above).** The record above, frozen at the
byte-for-byte parity this migrated block requires, calls Theorem 4.2 a cite-only documented axiom
and lists its file as `Quantum/SpinS/ShastryNoSSB.lean`. That is no longer current.
`shastry_no_symmetry_breaking_1d` is now a `theorem` in
`Quantum/SpinS/ShastryNoSSBReduction.lean`, with its statement unchanged, obtained by applying the
conditional capstone `shastry_no_symmetry_breaking_1d_of_energy_gain` to the documented axiom
`shastryEnergyGain` in that same file. The mathematical content is not discharged:
`shastryEnergyGain` is equivalent in strength to an `L`-uniform form of Theorem 4.2, and both
halves of that equivalence are now in Lean: the forward one as the conditional capstone, the
converse as `shastryEnergyGain_of_no_symmetry_breaking_1d` in the same file (axiom-free). So
`#print axioms shastry_no_symmetry_breaking_1d` still reports
`[propext, Classical.choice, Quot.sound, shastryEnergyGain]`. `ShastryNoSSB.lean` now carries only
the model, in four declarations (`ringCoupling`, `ringCoupling_self_star`,
`ringStaggeredSublattice`, `staggeredFieldChainHamiltonianS`); the variational layer the reduction
rests on (`chainGroundEnergy` and its evenness, concavity, zero-field maximality and
order-parameter sandwich) is in `Quantum/SpinS/ReversalSymmetricGroundEnergy.lean`. See the
Theorem 4.2 support entry of the Chapter 4 documented-axiom ledger for the current status.

<a id="record-616"></a>
## Record from former line 616

**Lean name:** <!-- legacy-detail-lean:start:616 -->`ringBondSquareLeftFieldHamiltonian` / `ringBondSquareLeftFieldHamiltonian_supportedOnLeft` / `ringBondSquareCrossingGen` / `ringBondSquareCrossingGen_supportedOnLeft` / `ringBondSquareFieldCrossing` / `ringBondSquareFieldCrossing_twoFieldConeRep` / `ringBondSquareTwoFieldWeight` / `ringBondSquareTwoFieldWeight_self` / `ringBondSquareTwoFieldWeight_isLimit`<!-- legacy-detail-lean:end:616 -->

**File:** <!-- legacy-detail-file:start:616 -->`Quantum/SpinS/RingReflectionBondSquareTwoFieldWeight.lean`<!-- legacy-detail-file:end:616 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:616 -->
**Bond-square DLS decomposition and two-field weight**
(`RingReflectionBondSquareTwoFieldWeight.lean`, Tasaki §4.1 (4.1.65)–(4.1.69), book p. 90,
bond-square DLS structure and Trotter limit / PR #4992, H_L corrected PR #4994): the left-half
Hamiltonian, field-dependent crossing generators, and the doubled Gibbs weight for the bond-square
model, all in the gauge spin basis. **Left half**: `ringBondSquareLeftFieldHamiltonian n N a` is the
intra-left bond terms `+Ŝ¹Ŝ¹ + Ŝ²Ŝ² + ½(Ŝ³ₓ + Ŝ³_y − a_x − a_y)²`, the single-ion `−(Ŝ³)²`, and the
boundary half-square `½(Ŝ³ₓ − a_x)²` (in repo DLS physical Heisenberg frame;

sign corrected from T̂-form transcription via the `(−1)ˣ` of `T̂³ = (−1)ˣŜ³` flipping α=1 to `+Ŝ¹Ŝ¹`
and converting longitudinal difference to sum-form;

left-supported, proved by `ringBondSquareLeftFieldHamiltonian_supportedOnLeft`;

exact physical coefficients deferred to PR-BS8;

PR #4994). **Crossing generators**: `ringBondSquareCrossingGen n N p z` is field-free on kinetic
slots `α = 0,1` and carries a bare central scalar shift `−z_x` on the longitudinal slot `α = 2`
(Tasaki (4.1.69), book p. 90), left-supported (`ringBondSquareCrossingGen_supportedOnLeft`).
**Two-field crossing**: `ringBondSquareFieldCrossing n N a b` is the field-dependent interaction
`∑_c θ(C_c(b))·C_c(a)` (with reflected `b` on the right, non-reflected `a` on the left),
instantiating the `RPTwoFieldConeRepS` shape (`ringBondSquareFieldCrossing_twoFieldConeRep`).
**Two-field weight**: `ringBondSquareTwoFieldWeight n N β a b` is the doubled Gibbs operator
`exp(−β·(H_L(a) + θ(H_L(b)) − crossing))` with independent left and right fields;

its diagonal collapse to a single field (`ringBondSquareTwoFieldWeight_self`) recovers the
symmetric-field DLS form;

its Trotter-limit representation (`ringBondSquareTwoFieldWeight_isLimit`, via `lieProductFormula`)
decomposes as `(exp(−(β/m)H_L(a)) · θ(exp(−(β/m)H_L(b))) · exp((β/m)·crossing))^m` converging as `m
→ ∞` (via the two-field crossing dependence). The physical coefficients and field identification are
deferred to PR-BS8 (the DLS form is Hamiltonian definition). This is PR-BS6 of the bond-square route
toward the reflection-positivity infrastructure for Theorem 4.2.
<!-- legacy-detail:end:616 -->

<a id="record-618"></a>
## Record from former line 618

**Lean name:** <!-- legacy-detail-lean:start:618 -->`ringBondSquareBondTermOf` / `ringBondSquareLeftBondSum` / `ringBondSquareRightBondSum` / `ringBondSquareFieldHamiltonian_eq_bondTermOf_sum` / `ringBondSquareFieldHamiltonian_ungauged_dls` / `ringBondSquareLeftBondSum_eq_leftCouplingBulk`<!-- legacy-detail-lean:end:618 -->

**File:** <!-- legacy-detail-file:start:618 -->`Quantum/SpinS/RingReflectionBondSquareUngaugedDLS.lean`<!-- legacy-detail-file:end:618 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:618 -->
**Bond-square ungauged DLS split** (`RingReflectionBondSquareUngaugedDLS.lean`, Tasaki §4.1
(4.1.48)/(4.1.69), book pp.86,90, ungauged bond-square DLS decomposition / PR #4995): the physical
bond-square field Hamiltonian reorganised without expanding any square into four-way directed-bond
classification, mirroring the linear ungauged DLS split
(`heisenbergHamiltonianS_ringCoupling_ungauged_dls`). **Per-bond term** `ringBondSquareBondTermOf n
N f x`: the summand `Ŝ¹ₓŜ¹_{x+1} + Ŝ²ₓŜ²_{x+1} + ½(Ŝ³ₓ + Ŝ³_{x+1} − f_x − f_{x+1})²` at the
staggered-field bare form `f` (no gauging). **Directed sums**: `ringBondSquareLeftBondSum`
(intra-left bonds `x+1 < n`), `ringBondSquareRightBondSum` (intra-right bonds `n ≤ x ∧ x+1 < 2n`) —
the four-way partition via `ringBondSquareFieldHamiltonian_eq_bondTermOf_sum` and the auxiliary
private `sum_four_way_split`. **Main theorem** `ringBondSquareFieldHamiltonian_ungauged_dls`: `Ĥ(h)
= intra-left + intra-right + crossing(n−1) + crossing(2n−1) − single-ion`, the bare-field ungauged
form before PR-BS8a-ii gauge conjugation into the DLS crux `H_L(a) + θ(H_L(b)) − crossing(a,b)`.
**Bridge** `ringBondSquareLeftBondSum_eq_leftCouplingBulk`: the directed intra-left sum equals the
merged `ringBondSquareLeftFieldHamiltonian`'s bulk double sum via `ringLeftCoupling`, the
bond-square analogue of `ringLeftHamiltonian_eq_leftBondSum` (PR-RP infra 18), aligning the ungauged
split with the DLS left half. Staggered-field visibility: `ringBondSquareStagField` (per-site
coefficient `(−1)^x h_x`, originally defined private in PR-BS1,
`RingReflectionBondSquareField.lean`) is de-privatized in this PR (PR-BS8a-i, #4995) for this
split's bond reorganisation. The gauge crux, physical-field identification, and reflection step are
deferred to PR-BS8a-ii and PR-BS8b. This is PR-BS8a-i of the bond-square route toward the
reflection-positivity infrastructure for Theorem 4.2.
<!-- legacy-detail:end:618 -->

<a id="record-619"></a>
## Record from former line 619

**Lean name:** <!-- legacy-detail-lean:start:619 -->`physBondSquareFieldOf` / `ringBondSquareStagField_physBondSquareFieldOf` / `rightGauge_conj_ringBondSquareFieldHamiltonian` / `rightGauge_conj_sub` / `rightGauge_conj_ringBondSquareBondTermOf_left` / `rightGauge_conj_ringBondSquareLeftBondSum` / `rightGauge_conj_ringBondSquareSingleIon` / `rightGauge_conj_ringBondSquareRightBondSum`<!-- legacy-detail-lean:end:619 -->

**File:** <!-- legacy-detail-file:start:619 -->`Quantum/SpinS/RingReflectionBondSquareGaugeCrux.lean`<!-- legacy-detail-file:end:619 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:619 -->
**Bond-square right-half gauge crux (G)** (`RingReflectionBondSquareGaugeCrux.lean`, Tasaki §4.1
(4.1.48)/(4.1.65)–(4.1.69), book pp.86,90, bond-square gauge conjugation and DLS crux / PR #4996):
conjugating the ungauged bond-square field Hamiltonian (BS8a-i) by the right-half Marshall gauge
into the two-field DLS operator `H_L(a) + θ(H_L(b)) − crossing(a,b)`. The crux input is the
**staggered wrapper** `physBondSquareFieldOf n a b z = (−1)ᶻ · physFieldOf n a b z`, a `(Fin (2n) →
ℝ)` carrying the spin-basis physical field whose bare (T̂-basis) split is the linear `physFieldOf a
b`;

feeding it into the bond-square Hamiltonian cancels the physical Hamiltonian's internal `(−1)ᶻ`
staggering via `((−1)ᶻ)² = 1` (**W1** `ringBondSquareStagField_physBondSquareFieldOf`), so the
effective field inside the square is the bare `physFieldOf a b`. The gauge distributes by
algebra-homomorphism laws with **no square expanded** in the bulk: intra-left bonds are gauge-fixed
to `H_L(a)` bulk;

intra-right bonds reindex to `θ(H_L(b))` bulk (the right-half double-sign cancellation);

only the two `O(1)` crossing bonds are completed `½(A−B)² = ½A² + ½B² − AB` into boundary
half-squares and the field crossing `−ringBondSquareFieldCrossing a b`. The single-ion term splits
left/right, right half reindexing to `θ` of the left. Assembling gives the **gauge crux (G)**
`rightGauge_conj_ringBondSquareFieldHamiltonian`, on which PR-BS8b builds the physical-field
identification and the one reflection step. Helper lemmas distribute conjugation over
difference/sum/product with localized gauge action. **De-privatised**
`sum_right_eq_sum_reflect_left` from `RingReflectionFieldPartition.lean` (reindexing the single-ion
right half via reflection bijection, statement and proof unchanged, visibility only to avoid
duplicate reindex lemma). This is PR-BS8a-ii of the bond-square route toward the
reflection-positivity infrastructure for Theorem 4.2.
<!-- legacy-detail:end:619 -->

<a id="record-620"></a>
## Record from former line 620

**Lean name:** <!-- legacy-detail-lean:start:620 -->`ringBondSquareFieldPartitionRe_physFieldOf` / `physBondSquareFieldOf_self` / `ringBondSquareFieldPartitionRe_reflection_step`<!-- legacy-detail-lean:end:620 -->

**File:** <!-- legacy-detail-file:start:620 -->`Quantum/SpinS/RingReflectionBondSquarePhysId.lean`<!-- legacy-detail-file:end:620 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:620 -->
**Bond-square physical-field identification and reflection step**
(`RingReflectionBondSquarePhysId.lean`, Tasaki §4.1 (4.1.48)–(4.1.51), book pp. 86–90, bond-square
physical-field identification and one reflection step / PR #4997): the physical identification of
the bond-square partition function with the two-field Gibbs trace, and the one reflection step in
sign-free classical form. **Physical identification** `ringBondSquareFieldPartitionRe_physFieldOf`
(bond-square physical-field identification, PR-BS8b): for the staggered wrapper
`physBondSquareFieldOf n a b` (carrying spin-basis staggering `(−1)^z · physFieldOf n a b z`), the
gauge crux (G) from PR-BS8a-ii conjugates the physical bond-square field Hamiltonian to the DLS
two-field operator, so `exp(−β·Ĥ^{BS}(physBondSquareFieldOf a b))` conjugates to
`exp(−β·Ĥ^{BS}(a,b))` via `Matrix.exp_units_conj` +
`rightGauge_conj_ringBondSquareFieldHamiltonian`, and trace invariance yields
`Z^{BS}(physBondSquareFieldOf a b) = Re Tr W^{BS}(a,b)`. **Sign-free classical collapses** (the crux
of why bond-square avoids signed-copy variants): the two internal staggered relabels of the wrapper
cancel (`physBondSquareFieldOf_eq_relabel`, private bridge), collapsing the three field pairs of the
reflection step to Tasaki's classical sign-free mirrors (4.1.50) (book p. 86):
`physBondSquareFieldOf_self` (L1, arbitrary physical field decomposed as wrapper split),
`physBondSquareFieldOf_diag_left` (L2, left reflection, private), `physBondSquareFieldOf_diag_right`
(L3, right reflection, private). **One reflection step**
`ringBondSquareFieldPartitionRe_reflection_step` (sign-free classical form, no staggered relabel on
right): for `β ≥ 0`, `Z^{BS}(g)² ≤ Z^{BS}(reflectLeft n g)·Z^{BS}(reflectRight n g)` — the finite-β
partition-function form of Tasaki's bond-square reflection bound (4.1.51) — obtained by expressing
`g` as the wrapper split via L1, applying the physical identification three times at the three field
pairs (with L2/L3 collapsing to the sign-free classical mirrors), and reducing to the BS7 capstone
`ringBondSquareTwoFieldWeight_reflection_cauchySchwarz` (proof pp. 89–93;

DLS 1978 §2–3). The `β → ∞` limit yields the ground-state reflection bound. The private
staggered-relabel bridge `physBondSquareFieldOf_eq_relabel` is the key: it exhibits the wrapper as
the staggered relabel `P ∘ physFieldOf` of the linear split field, so the composition `P ∘
physFieldOf ∘ P` (two relabels on the right-field slots) simplifies to the bare sign-free reflected
copies, **no signed-copy variants** (contrast linear route where the right-side field must carry a
sign and produce signed mirrors). This is PR-BS8b of the bond-square route toward the
reflection-positivity infrastructure for Theorem 4.2.
<!-- legacy-detail:end:620 -->
